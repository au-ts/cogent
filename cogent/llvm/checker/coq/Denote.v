From Coq Require Import List ZArith String.

From ExtLib Require Import Structures.Monads Structures.Functor Structures.Reducible Data.Map.FMapAList.
From ITree Require Import ITree Events.State Events.Exception.
From Vellvm Require Import Util Utils.Error.

From Checker Require Import Cogent Utils.Instances Utils.Fail.

Import Monads.
Import ListNotations.
Import MonadNotation.
Import FunctorNotation.
Local Open Scope monad_scope.
Local Open Scope string_scope.

Inductive uval : Set :=
| UPrim (l : lit)
| URecord (us : list (uval * repr))
| UUnit
| UPtr (a : addr) (r : repr)
| UFunction (f : name).

Definition ctx : Type := list uval.

Variant CallE : Type -> Type :=
| Call (f : uval) (a : uval) : CallE uval.

Variant MemE : Type -> Type :=
| LoadMem (a : addr) : MemE (option uval)
| StoreMem (a : addr) (u : uval) : MemE unit.

Definition FailE := exceptE string.

Definition CogentE := CallE +' MemE +' FailE.

Definition CogentL1 := MemE +' FailE.
Definition CogentL2 := FailE.

Section Denote.

  Definition option_bind {A T} (x : option A) (f : A -> T) (m : string) : itree CogentE T := 
    match x with
    | Some y => ret (f y)
    | None => throw m
    end.

  Definition extract_prim (x : uval) : itree CogentE lit :=
    match x with
    | UPrim v => ret v
    | _ => throw "not a prim"
    end.
  
  Definition denote_prim (op : prim_op) (xs : list uval) : itree CogentE uval :=
    xs' <- map_monad extract_prim xs ;;
    option_bind (eval_prim_op op xs') UPrim "op error".

  Definition access_member (fs : list (uval * repr)) (f : nat) : itree CogentE uval :=
    option_bind (nth_error fs f) fst "invalid member access".

  (* is this built-in somewhere? *)
  Fixpoint list_upd {T} (l : list T) (n : nat) (r : T) : list T :=
    match l, n with
    | x::xs, 0 => r::xs
    | x::xs, S u => x::(list_upd xs u r)
    | _, _ => l
    end.

  Fixpoint denote_expr (γ : ctx) (e : expr) : itree CogentE uval :=
    (* define some nested functions that are mutually recursive with denote_expr *)
    let fix denote_member (γ : ctx) (e : expr) (f : nat) {struct e} : itree CogentE (uval * uval) :=
      r <- denote_expr γ e ;;
      m <- match r with
      | URecord fs => access_member fs f
      | UPtr p r =>
          m <- trigger (LoadMem p) ;;
          match m with
          | Some (URecord fs) => access_member fs f
          | _ => throw "invalid memory access"
          end
      | _ => throw "expression is not a record"
      end ;;
      ret (r, m) in
    match e with
    | Prim p xs =>
        xs' <- map_monad (denote_expr γ) xs ;;
        denote_prim p xs'
    | Lit l => ret (UPrim l)
    | Var i => option_bind (nth_error γ i) id "unknown variable"
    | Let a b =>
        a' <- denote_expr γ a ;;
        denote_expr (a' :: γ) b
    | Unit => ret UUnit
    | If x t e =>
        x' <- denote_expr γ x ;;
        match x' with
        | UPrim (LBool b) => denote_expr γ (if b then t else e)
        | _ => throw "expression is not a boolean"
        end
    | Cast τ e =>
        e' <- denote_expr γ e ;;
        match e' with
        | UPrim l => option_bind (cast_to τ l) UPrim "invalid cast"
        | _ => throw "invalid cast"
        end
    | Struct ts xs =>
        vs <- map_monad (denote_expr γ) xs ;;
        ret (URecord (combine vs (map type_repr ts)))
    | Member e f => snd <$> denote_member γ e f
    | Take x f e => 
        '(r, m) <- denote_member γ x f ;;
        denote_expr (m :: r :: γ) e
    | Put x f e =>
        x' <- denote_expr γ x ;;
        e' <- denote_expr γ e ;;
        (* can we avoid code repetition between this and denote_member? *)
        match x' with
        | URecord fs =>
            rep <- option_bind (nth_error fs f) snd "invalid member access" ;;
            ret (URecord (list_upd fs f (e', rep)))
        | UPtr p r =>
            m <- trigger (LoadMem p) ;;
            match m with
            | Some (URecord fs) =>
                rep <- option_bind (nth_error fs f) snd "invalid member access" ;;
                trigger (StoreMem p (URecord (list_upd fs f (e', rep)))) ;;
                ret (UPtr p r)
            | _ => throw "invalid memory access"
            end
        | _ => throw "expression is not a record"
        end
    | Fun n ft => ret (UFunction n)
    | App x y =>
        f <- denote_expr γ x ;;
        a <- denote_expr γ y ;;
        trigger (Call f a)
    end.

  Definition function_denotation := uval -> itree CogentE uval.

  Definition denote_fun (b : expr) : function_denotation :=
    fun a => denote_expr [a] b.

  Definition module := alist name function_denotation.

  Definition prog_to_module (p : cogent_prog) : module :=
    map (fun '(FunDef n t rt b) => (n, denote_fun b)) p.

End Denote.

From ExtLib Require Import Structures.Maps.

Section Interpretation.

  Definition handle_call (m : module) : CallE ~> itree CogentE :=
    fun _ '(Call f a) =>
      match f with
      | UFunction fn => 
          match alist_find _ fn m with
          | Some f' => f' a
          | None => throw ("unknown function " ++ fn)
          (* or maybe it's an abstract function? *)
          end
      | _ => throw "expression is not a function"
      end.

  Definition interp_call (m : module) (entry_f : uval) (entry_a : uval) : itree CogentL1 uval :=
    mrec (handle_call m) (Call entry_f entry_a).

  Definition memory := alist addr uval.
  Definition empty_memory : memory := empty.
  Definition dummy_memory : memory := 
    alist_add _ 23 (URecord [(UPrim (LU8 5), RPrim (Num U8))]) empty_memory.

  Definition handle_mem : MemE ~> stateT memory (itree CogentL2) :=
    fun _ e σ =>
      match e with
      | LoadMem a => ret (σ, alist_find _ a σ)
      | StoreMem a u => ret (alist_add _ a u σ, tt)
      end.
  
  Definition interp_mem : itree CogentL1 ~> stateT memory (itree CogentL2) :=
    interp_state (case_ handle_mem pure_state).

  Definition handle_failure : FailE ~> failT (itree void1) :=
    fun _ '(Throw m) => ret (inl m).

  (* from Helix *)
  Definition inject_signature {E} : void1 ~> E := fun _ (x : void1 _) => match x with end.
  Hint Unfold inject_signature : core.

  Definition interp_cogent {E} (m : module) 
                               (entry_f : uval) (entry_a : uval)
                               (mem : memory) 
                             : failT (itree E) (memory * uval) :=
    let l1 := interp_call m entry_f entry_a in
    let l2 := interp_mem _ l1 mem in
    let l3 := interp handle_failure l2 in
    translate inject_signature l3.

  Definition run_cogent (p : cogent_prog) 
                        (entry_f : uval) (entry_a : uval) 
                      : failT (itree void1) (memory * uval) :=
    interp_cogent (prog_to_module p) entry_f entry_a dummy_memory.

End Interpretation.
