From Coq Require Import List ZArith String.

From ExtLib Require Import Structures.Monads Structures.Functor Structures.Reducible.
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
| UPtr (a : addr) (r : repr).

Variant VarE : Type -> Type :=
| PeekVar (i : index) : VarE uval
| PushVar (u : uval) : VarE unit
| PopVar : VarE unit.

Variant MemE : Type -> Type :=
| LoadMem (a : addr) : MemE (option uval)
| StoreMem (a : addr) (u : uval) : MemE unit.

Definition FailE := exceptE string.

Definition CogentE := VarE +' MemE +' FailE.

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
  
  Definition denote_bind {A} (v : uval) (b : itree CogentE A) : itree CogentE A :=
    trigger (PushVar v) ;;
    b' <- b ;;
    trigger PopVar ;; (* do we actually need to do this? *)
    ret b'.

  (* is this built-in somewhere? *)
  Fixpoint list_upd {T} (l : list T) (n : nat) (r : T) : list T :=
    match l, n with
    | x::xs, 0 => r::xs
    | x::xs, S u => x::(list_upd xs u r)
    | _, _ => l
    end.

  Fixpoint denote_expr (e : expr) : itree CogentE uval :=
    (* define some nested functions that are mutually recursive with denote_expr *)
    let fix denote_member (e : expr) (f : nat) : itree CogentE (uval * uval) :=
      e' <- denote_expr e ;;
      f' <- match e' with
      | URecord fs => access_member fs f
      | UPtr p r =>
          m <- trigger (LoadMem p) ;;
          match m with
          | Some (URecord fs) => access_member fs f
          | _ => throw "invalid memory access"
          end
      | _ => throw "expression is not a record"
      end ;;
      ret (e', f') in
    match e with
    | Prim op os =>
        os' <- map_monad denote_expr os ;;
        denote_prim op os'
    | Lit l => ret (UPrim l)
    | Var i => trigger (PeekVar i)
    | Let e b => denote_expr e >>= flip denote_bind (denote_expr b)
    | Unit => ret UUnit
    | If c t e =>
        c' <- denote_expr c ;;
        match c' with
        | UPrim (LBool b) => denote_expr (if b then t else e)
        | _ => throw "expression is not a boolean"
        end
    | Cast t e =>
        e' <- denote_expr e ;;
        match e' with
        | UPrim l => option_bind (cast_to t l) UPrim "invalid cast"
        | _ => throw "invalid cast"
        end
    | Struct ts es =>
        es' <- map_monad denote_expr es ;;
        ret (URecord (combine es' (map type_repr ts)))
    | Member e f => snd <$> denote_member e f
    | Take x f e => denote_member x f >>= fold denote_bind (denote_expr e)
    | Put x f e =>
        x' <- denote_expr x ;;
        e' <- denote_expr e ;;
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

    end.

  Definition denote_fun (b : expr) : uval -> itree CogentE uval :=
    fun a =>
      trigger (PushVar a) ;;
      b' <- denote_expr b ;;
      trigger PopVar ;;
      ret b'.

End Denote.

From ExtLib Require Import Data.Map.FMapAList Core.RelDec Data.String Structures.Maps.

Section Interpretation.

  Definition locals := list uval.
  Definition empty_locals : locals:= [].
  
  Definition handle_var : VarE ~> stateT locals (itree (MemE +' FailE)) :=
    fun _ e γ =>
      match e with
      | PeekVar i =>
          match nth_error γ i with
          | Some v => ret (γ, v)
          | None => throw "unknown variable"
          end
      | PushVar u => ret (u :: γ, tt)
      | PopVar => ret (tl γ, tt)
      end.

  Definition interp_var : itree CogentE ~> stateT locals (itree (MemE +' FailE)) :=
    interp_state (case_ handle_var pure_state).

  Definition memory := alist addr uval.
  Definition empty_memory : memory := empty.
  Definition dummy_memory : memory := 
    alist_add _ 23 (URecord [(UPrim (LU8 5), RPrim (Num U8))]) empty_memory.

  Definition handle_mem : MemE ~> stateT memory (itree FailE) :=
    fun _ e σ =>
      match e with
      | LoadMem a => ret (σ, alist_find _ a σ)
      | StoreMem a u => ret (alist_add _ a u σ, tt)
      end.
  
  Definition interp_mem : itree (MemE +' FailE) ~> stateT memory (itree FailE) :=
    interp_state (case_ handle_mem pure_state).

  Definition handle_failure : FailE ~> failT (itree void1) :=
    fun _ '(Throw m) => ret (inl m).

  (* from Helix *)
  Definition inject_signature {E} : void1 ~> E := fun _ (x : void1 _) => match x with end.
  Hint Unfold inject_signature : core.

  Definition interp_cogent {E A} (l0 : itree CogentE A) (vars : locals) (mem : memory) : failT (itree E) (memory * (locals * A)) :=
    let l1 := interp_var _ l0 vars in
    let l2 := interp_mem _ l1 mem in
    let l3 := interp handle_failure l2 in
    translate inject_signature l3.

  Definition run_cogent (a : uval) (f : expr) : failT (itree void1) (memory * (locals * uval)) :=
    interp_cogent (denote_fun f a) empty_locals dummy_memory.

End Interpretation.
