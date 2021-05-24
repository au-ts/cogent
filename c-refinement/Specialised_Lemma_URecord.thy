(*
 * Copyright 2018, Data61
 * Commonwealth Scientific and Industrial Research Organisation (CSIRO)
 * ABN 41 687 119 230.
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(DATA61_BSD)
 *)

theory Specialised_Lemma_URecord
imports
  Read_Table
  SpecialisedLemmaTactic
begin

context update_sem_init
begin

text\<open> lemma-generation for URecord (Member, Take, and Put).\<close>
(* 


Generally in this file, custom means custom layout, default means default layout

They are 4 types of lemmas: Put, LetPut for updating a field (Writable only), and 
Take (any sigil except Readonly)/Member (readonly only) for accessing a field.

Some functions are shared between Put and LetPut lemmas, as they
have very similar statements. Functions relevant for both Put and LetPut
have a name involving put_let_put.

Similarly, Take and Member are very similar so we have names based on take_member


*)


ML \<open>
(* cogent expressions whose correspondence is stated by the lemmas *)
val let_put_cogent_expr = @{term "\<lambda> field_num. (expr.Let (Put (Var x) field_num (Var v)) e)"}
val put_cogent_expr = @{term "(\<lambda> field_num. Put (Var x) field_num (Var v))"}
val take_cogent_expr = @{term "(\<lambda> field_num. Take (Var x) field_num e)"}
val member_cogent_expr = @{term "Member (Var x)"}
\<close>

(* monadic expressions whose correspondence is stated by the lemmas *)
ML \<open>
val put_default_prog = @{term " \<lambda> is_valid_struct heap_struct_update field_setter.
    (do
         ptr \<leftarrow> gets (\<lambda>_. x');
        _ \<leftarrow> guard (\<lambda>s. is_valid_struct s ptr);
        _ \<leftarrow> modify (heap_struct_update (\<lambda>a. a(ptr := field_setter (\<lambda>a. v') (a ptr))));
        gets (\<lambda>_. ptr)
        od) "}

val let_put_default_prog =  @{term " \<lambda> is_valid_struct heap_struct_update field_setter.
    (do
           ptr \<leftarrow> gets (\<lambda>_. x');
       _ \<leftarrow> guard (\<lambda>s. is_valid_struct s ptr);
       _ \<leftarrow> modify (heap_struct_update (\<lambda>a. a(ptr := field_setter (\<lambda>a. v') (a ptr))));
       ptr' \<leftarrow> gets (\<lambda>_. ptr);
       e' ptr'
       od) "}

val take_unboxed_default_prog = @{term "\<lambda>  getter. gets (\<lambda>s. getter x') >>= e'"}
val take_boxed_default_prog = @{term 
         "\<lambda> is_valid getter heap. (do _ \<leftarrow> guard (\<lambda>s. is_valid s x');
           z \<leftarrow> gets (\<lambda>s. getter (heap s x')); e' z od)"} 
val member_default_prog = @{term 
     "\<lambda> is_valid getter heap. (do _ \<leftarrow> guard (\<lambda>s. is_valid s x'); 
        gets (\<lambda>s. getter (heap s x')) od)"} 


\<close>

ML \<open>

val take_custom_prog =   @{term "\<lambda> getter.
     (do v <- getter x' ;
         z <- gets (\<lambda>_. v) ;
         e' z
      od) " }

val member_custom_prog = @{term "\<lambda> getter. (do z <- getter x';  gets (\<lambda>_. z)   od) "}

val put_custom_prog =  @{term "\<lambda> setter.
 (do ptr <- gets (\<lambda>_. x');
     _ <- setter ptr v'  ;
     _ <- gets (\<lambda>_. ());
     gets (\<lambda>_. ptr)
  od)" } 

val let_put_custom_prog =  @{term "\<lambda> setter.
 (do ptr <- gets (\<lambda>_. x');
     _ <- setter ptr v'  ;
     _ <- gets (\<lambda>_. ());     
    ptr' \<leftarrow> gets (\<lambda>_. ptr);
       e' ptr'
  od)" } 
\<close>


(* 

Set of assumptions for the different lemmas

*)

ML \<open>
(* state_rel, isa_sigil, ty, field_ty, isa_field_num, isa_struct_leng *)
type assumption_args = term * term * typ * typ * term * term

local 

(* Assumptions common to all kind of lemmas *)
fun common_assumptions isa_sigil ty = 
 let

  (* define meta-assumptions in specialised corres lemmas.*)
  val h1 = @{mk_term "\<Gamma>' ! x = Some (TRecord typ ?isa_sigil)" isa_sigil} isa_sigil;
  val h2 = @{mk_term "val_rel (\<gamma>!x) ?x'" x'} (Free ("x'", ty));
  val h3 = strip_atype @{term "\<lambda> isa_sigil ty . type_rel (type_repr (TRecord typ isa_sigil)) ty"}
            $ isa_sigil $ (Const ("Pure.type", Term.itselfT ty) |> strip_atype);

  
 in
  (h1, h2, h3)
end

(* Assumptions common to take and member lemmas *)
fun take_member_assumptions isa_sigil ty field_ty isa_field_num =
(* Generate specialised Take lemmas for the Writables and Unboxeds.*)
 let
  val (ass1, ass3, ass4) = common_assumptions isa_sigil ty

  val ass5 = strip_atype @{term "\<lambda> field_num ty . 
            type_rel (type_repr (fst (snd (typ ! field_num)))) ty"}
            $ isa_field_num $ (Const ("Pure.type", Term.itselfT field_ty(* field_ty *)) |> strip_atype);
  
 in
  (ass1, ass3, ass4, ass5)
 end;

(* Assumptions common to Put and LetPut lemmas *)
fun put_let_put_assumptions ty field_ty isa_int_struct_leng =
 let
  val (ass2, ass4, ass3) = common_assumptions @{term "Boxed Writable"} ty
  val ass1 = @{term "0, [], {} \<turnstile> \<Gamma>' \<leadsto> \<Gamma>x | \<Gamma>e"};
  val ass5 = strip_atype @{term "\<lambda> v' . val_rel (\<gamma>!v) v'"} $ Free ("v'", field_ty);

  val ass78 = strip_atype @{term "\<lambda> leng . length typ = leng"} $ isa_int_struct_leng;
 in
   (ass1, ass2, ass3, ass4, ass5, ass78)
end

in

(* Assumptions for Take lemmas *)
fun take_assumptions
  
   ((state_rel, isa_sigil, ty, field_ty, isa_field_num, _) : assumption_args)  ctxt
   =
  let
  val (ass1, ass3, ass4, ass5) = take_member_assumptions isa_sigil ty field_ty isa_field_num;
  val ass2 = @{term    "0, [], {} \<turnstile> \<Gamma>' \<leadsto> \<Gamma>x | \<Gamma>e"};
  val ass6 = strip_atype @{term "\<lambda> field_num . \<Xi>', 0, [], {}, \<Gamma>' \<turnstile> Take (Var x) field_num e : te"} $ isa_field_num;
  val ass7 = strip_atype @{term "\<lambda> isa_sigil . \<Xi>', 0, [], {}, \<Gamma>x \<turnstile> (Var x) : TRecord typ isa_sigil"} $ isa_sigil;
(*
=======
  (* define auxiliary values and functions.*)
  val struct_C_nm     = get_ty_nm_C uval;
  val struct_ty       = Syntax.read_typ ctxt struct_C_nm;
  val struct_C_ptr_ty = Syntax.read_typ ctxt (struct_C_nm ^ " ptr");
  val heap            = Symtab.lookup (HeapInfo.get (Proof_Context.theory_of ctxt)) file_nm
                        |> Utils.the' "heap in mk_specialised_corres_take failed."
                        |> #heap_info;
  val field_info      = Symtab.lookup (#structs heap) struct_C_nm
                        |> Utils.the' "field_info in mk_specialised_corres_take failed."
                        |> #field_info;
  val nth_field       = List.nth (field_info, field_num);
  val field_ty        = #field_type nth_field;
  val isa_field_num   = encode_isa_int ctxt field_num;
  val get_clean_term  = fn str:string => Syntax.read_term ctxt str |> strip_atype;
  val state_rel       = get_clean_term "state_rel";
  val field_getter    = #getter nth_field;
  val ml_sigil        = get_uval_sigil uval;
  val isa_sigil = case ml_sigil of
                ReadOnly => @{term "Boxed ReadOnly ptrl"}
              | Writable => @{term "Boxed Writable ptrl"}
              | Unboxed  => @{term "Unboxed"}
  (* Unboxed-Take and Boxed-Take use different types.*)
  val ty = case ml_sigil of
            Writable => struct_C_ptr_ty
          | Unboxed  => struct_ty
          | _        => error "ty in mk_specialised_corres_take failed.";

  (* define meta-assumptions in specialised corres lemmas.*)
  val ass1 = @{mk_term "\<Gamma>' ! x = Some (TRecord typ ?isa_sigil)" isa_sigil} isa_sigil;
  val ass2 = @{term    "0, [], {} \<turnstile> \<Gamma>' \<leadsto> \<Gamma>x | \<Gamma>e"};
  val ass3 = @{mk_term "val_rel (\<gamma>!x) ?x'" x'} (Free ("x'", ty));
  val ass4 = strip_atype @{term "\<lambda> isa_sigil ty . type_rel (type_repr (TRecord typ isa_sigil)) ty"}
            $ isa_sigil $ (Const ("Pure.type", Term.itselfT ty) |> strip_atype);
  val ass5 = strip_atype @{term "\<lambda> field_num ty . type_rel (type_repr (fst (snd (typ ! field_num)))) ty"}
            $ isa_field_num $ (Const ("Pure.type", Term.itselfT field_ty) |> strip_atype);
  val ass6 = strip_atype @{term "\<lambda> field_num . \<Xi>', 0, [], {}, \<Gamma>' \<turnstile> Take (Var x) field_num e : te"} $ isa_field_num;
  val ass7 = strip_atype @{term "\<lambda> isa_sigil . \<Xi>', 0, [], {}, \<Gamma>x \<turnstile> (Var x) : TRecord typ isa_sigil"} $ isa_sigil;
>>>>>>> origin/dargenttyping
*)
  val ass8 = strip_atype @{term "\<lambda> isa_sigil field_num .
             (\<Xi>', 0, [], {}, Some (fst (snd (typ ! field_num))) #
              Some (TRecord (typ[field_num := (fst (typ ! field_num), fst (snd (typ ! field_num)), taken)]) isa_sigil) # \<Gamma>e \<turnstile> e : te)"}
            $ isa_sigil $ isa_field_num;
  (* For some reason, I cannot use the mk-term antiquotation for ass9.*)
  val ass9 = strip_atype @{term "\<lambda> field_num . 0, [], {} \<turnstile> fst (snd (typ ! field_num)) :\<kappa> k"} $ isa_field_num;
  val ass10= @{term "(S \<in> k \<or> taken = Taken)"};
  (* ass11 involves a bit ugly hacks. Maybe I can use \<lambda> for field_num instead of \<And>.*)
  val ass11 = let
               fun rep_Bound_n_with n new = strip_1qnt o
                   (Term.map_aterms (fn trm => if trm = Bound n then new else trm));
              in
              (strip_atype @{term "\<And> state_rel isa_sigil field_num vf z. val_rel vf z \<Longrightarrow>
               corres state_rel e (e' z) \<xi> (vf # (\<gamma>!x) # \<gamma>) \<Xi>'
                (Some (fst (snd (typ ! field_num))) # Some (TRecord (typ[field_num := (fst (typ ! field_num), fst (snd (typ ! field_num)), taken)])
                isa_sigil) # \<Gamma>e) \<sigma> s"})
               |> rep_Bound_n_with 4 state_rel
               |> rep_Bound_n_with 3 isa_sigil
               |> rep_Bound_n_with 2 isa_field_num
               |> up_ty_of_qnt "z" field_ty ctxt
              end;
  val prms = map (HOLogic.mk_Trueprop o strip_atype)
   [ass1, ass2, ass3, ass4, ass5, ass6, ass7, ass8, ass9, ass10] @ [ass11];
  in
    prms
end

(* assumptions for member *)
fun member_assumptions
 ((_, isa_sigil, ty, field_ty, isa_field_num, _) : assumption_args) (_ : Proof.context)
   =
  let
    val (ass1, ass3, ass4, ass5) = take_member_assumptions isa_sigil ty field_ty isa_field_num;
    val ass6 = @{term "\<lambda> isa_field_num . \<Xi>', 0, [], {}, \<Gamma>' \<turnstile> Member (Var x) isa_field_num : te"} $ isa_field_num;
    val ass7 = @{term " \<Xi>', 0, [], {}, \<Gamma>' \<turnstile> Var x : TRecord typ (Boxed ReadOnly ptrl)"};
    val prms = map (HOLogic.mk_Trueprop o strip_atype) [ass1, ass3, ass4, ass5, ass6, ass7];
  in
    prms
  end

fun let_put_assumptions 
  ((state_rel, _, ty, field_ty, isa_field_num, isa_struct_leng) : assumption_args)(_ : Proof.context)
   =
  let
    val (ass1, ass2, ass3, ass4, ass5, ass8) =  put_let_put_assumptions ty field_ty isa_struct_leng;
    val ass6 = strip_atype @{term "\<lambda> field_num .
             \<Xi>', 0, [], {}, \<Gamma>' \<turnstile> expr.Let (Put (Var x) field_num (Var v)) e : ts"} $ isa_field_num;
    val ass7 = strip_atype @{term "\<lambda> field_num .
             \<Xi>', 0, [], {}, \<Gamma>x \<turnstile> Put (Var x) field_num (Var v) :
                         TRecord (typ[field_num := (fst (typ ! field_num), fst (snd (typ ! field_num)), Present)]) (Boxed Writable ptrl)"} $ isa_field_num;
    val ass9 = let
              fun rep_Bound_n_with n new = strip_1qnt o
                   (Term.map_aterms (fn trm => if trm = Bound n then new else trm));
             in
              strip_atype @{term "\<And> state_rel field_num \<sigma> s.
               corres state_rel e (e' x') \<xi> ((\<gamma>!x) # \<gamma>) \<Xi>'
               (Some (TRecord (typ[field_num := (fst (typ ! field_num), fst (snd (typ ! field_num)), Present)]) (Boxed Writable ptrl)) # \<Gamma>e) \<sigma> s"}
               |> rep_Bound_n_with 3 state_rel |> rep_Bound_n_with 2 isa_field_num
             end;

  
    val prms = map (HOLogic.mk_Trueprop o strip_atype)
            [ass1, ass2, ass3, ass4, ass5, ass6, ass7, ass8] @ [ass9];
  in
    prms
  end


fun put_assumptions 
 ((_, _, ty, field_ty, isa_field_num, isa_struct_leng) : assumption_args) (_ : Proof.context)
=
  let
    val (ass1, ass2, ass3, ass4, ass5, ass7) =  put_let_put_assumptions ty field_ty isa_struct_leng;
    val ass6 = strip_atype @{term "\<lambda> field_num .
             \<Xi>', 0, [], {}, \<Gamma>' \<turnstile> Put (Var x) field_num (Var v) :
                         TRecord (typ[field_num := (fst (typ ! field_num), fst (snd (typ ! field_num)), Present)]) (Boxed Writable ptrl)"} $ isa_field_num;
    val prms = map (HOLogic.mk_Trueprop o strip_atype)
            [ass1, ass2, ass3, ass4, ass5, ass6, ass7];
  in
    prms
  end

end

\<close>


(* Generation of the statements *)


ML \<open>
 fun mk_corres_statement cogent_expr main_prog prms state_rel isa_field_num ctxt =
  let
    val cncl =
     strip_atype @{term "\<lambda> cogent state_rel field_num prog .
         corres state_rel
          (cogent field_num)
          prog
           \<xi> \<gamma> \<Xi>' \<Gamma>' \<sigma> s"}
         $ cogent_expr $ state_rel $ isa_field_num $ main_prog
         |> HOLogic.mk_Trueprop
    val term = mk_meta_imps prms cncl ctxt |> Syntax.check_term ctxt;
  
 in term end
\<close>

ML \<open>
fun mk_specialised_corres_statement get_assumptions
  uval field_num cogent_expr (total_num, main_prog, (field_ty : typ)) ctxt =
let 
  val state_rel  = Syntax.read_term ctxt "state_rel" |> strip_atype; 
  val isa_field_num             = encode_isa_int ctxt field_num;
  val isa_struct_leng = encode_isa_int ctxt total_num
  val struct_C_nm     = get_ty_nm_C uval;
  val ml_sigil        = get_uval_sigil uval;  
  val isa_sigil = case ml_sigil of
                Boxed (ReadOnly, _) => @{term "Boxed ReadOnly ptrl"}
              | Boxed (Writable, _) => @{term "Boxed Writable ptrl"}
              | Unboxed  => @{term "Unboxed"}
  val ty = case ml_sigil of
            Boxed(_, _) => Syntax.read_typ ctxt (struct_C_nm ^ " ptr")
          | Unboxed  => Syntax.read_typ ctxt struct_C_nm    

  val prms = get_assumptions 
   ((state_rel, isa_sigil, ty, field_ty, isa_field_num, isa_struct_leng) : assumption_args)
   ctxt;
  val term = mk_corres_statement cogent_expr main_prog prms state_rel isa_field_num ctxt
 
 in term
 end;
\<close>

ML\<open>
 fun mk_specialised_corres_let_put_aux (field_num:int) uval args ctxt =
 let
  val _ = tracing "mk_specialised_corres_let_put_aux"
  val _ =
   case get_uval_sigil uval of
      Boxed(Writable, _) => ()
    | _ => error "LetPut is supported for Writable only"
  
  val cogent_expr = let_put_cogent_expr
 in
    mk_specialised_corres_statement let_put_assumptions uval field_num cogent_expr args 
       ctxt
 end

fun mk_specialised_corres_put_aux (field_num:int) uval args ctxt =
 let
  val _ = tracing "mk_specialised_corres_let_put_aux"
  val _ =
   case get_uval_sigil uval of
      Boxed(Writable, _) => ()
    | _ => error "Put is supported for Writable only"
  val cogent_expr = put_cogent_expr
 in
    mk_specialised_corres_statement put_assumptions uval field_num cogent_expr args 
       ctxt
 end

fun mk_specialised_corres_take_aux (field_num:int) uval args ctxt =
 let
  val _ = tracing "mk_specialised_corres_take_aux"
  val _ =
   case get_uval_sigil uval of
      Boxed(ReadOnly, _) => error "ReadOnly is not supported by cncl in mk_specialised_corres_take_aux. :("
    | _ => ()
  val cogent_expr = take_cogent_expr
 in
    mk_specialised_corres_statement take_assumptions uval field_num cogent_expr args 
       ctxt
 end

fun mk_specialised_corres_member_aux (field_num:int) uval args ctxt =
 let
  val _ = tracing "mk_specialised_corres_member_aux"
  val _ =  case get_uval_sigil uval of
      Boxed(ReadOnly, _) => ()
    | _ => error "Member is supported for ReadOnly only.";
  val cogent_expr = member_cogent_expr
 in
    mk_specialised_corres_statement member_assumptions uval field_num cogent_expr args 
       ctxt
 end
(*
=======
  (* define assumptions *)
  val ass1 = @{term "0, [], {} \<turnstile> \<Gamma>' \<leadsto> \<Gamma>x | \<Gamma>e"};
  val ass2 = @{term "\<Gamma>' ! x = Some (TRecord typ (Boxed Writable ptrl))"};
  val ass3 = (strip_atype @{term "\<lambda> struct_C_ptr_ty .
             type_rel (type_repr (TRecord typ (Boxed Writable ptrl))) struct_C_ptr_ty"}) $
             (Const ("Pure.type", Term.itselfT struct_C_ptr_ty) |> strip_atype);
  val ass4 = strip_atype @{term "\<lambda> x' . val_rel (\<gamma>!x) x'"} $ Free ("x'", struct_C_ptr_ty);
  val ass5 = strip_atype @{term "\<lambda> v' . val_rel (\<gamma>!v) v'"} $ Free ("v'", field_ty);
  val ass6 = strip_atype @{term "\<lambda> field_num .
             \<Xi>', 0, [], {}, \<Gamma>' \<turnstile> Put (Var x) field_num (Var v) :
                         TRecord (typ[field_num := (fst (typ ! field_num), fst (snd (typ ! field_num)), Present)]) (Boxed Writable ptrl)"} $ isa_int;
  val ass7 = strip_atype @{term "\<lambda> leng . length typ = leng"} $ isa_int_struct_leng;
  val prms = map (HOLogic.mk_Trueprop o strip_atype)
            [ass1, ass2, ass3, ass4, ass5, ass6, ass7];
>>>>>>> origin/dargenttyping

*)
\<close>


(* Building the data for the default layout *)




ML \<open>
(*
=======
  (* define assumptions *)
  val ass1 = @{term "0, [], {} \<turnstile> \<Gamma>' \<leadsto> \<Gamma>x | \<Gamma>e"};
  val ass2 = @{term "\<Gamma>' ! x = Some (TRecord typ (Boxed Writable ptrl))"};
  val ass3 = (strip_atype @{term "\<lambda> struct_C_ptr_ty .
             type_rel (type_repr (TRecord typ (Boxed Writable ptrl))) struct_C_ptr_ty"}) $
             (Const ("Pure.type", Term.itselfT struct_C_ptr_ty) |> strip_atype);
  val ass4 = strip_atype @{term "\<lambda> x' . val_rel (\<gamma>!x) x'"} $ Free ("x'", struct_C_ptr_ty);
  val ass5 = strip_atype @{term "\<lambda> v' . val_rel (\<gamma>!v) v'"} $ Free ("v'", field_ty);
  val ass6 = strip_atype @{term "\<lambda> field_num .
             \<Xi>', 0, [], {}, \<Gamma>' \<turnstile> expr.Let (Put (Var x) field_num (Var v)) e : ts"} $ isa_int;
  val ass7 = strip_atype @{term "\<lambda> field_num .
             \<Xi>', 0, [], {}, \<Gamma>x \<turnstile> Put (Var x) field_num (Var v) :
                         TRecord (typ[field_num := (fst (typ ! field_num), fst (snd (typ ! field_num)), Present)]) (Boxed Writable ptrl)"} $ isa_int;
  val ass8 = strip_atype @{term "\<lambda> leng . length typ = leng"} $ isa_int_struct_leng;
  val ass9 = let
              fun rep_Bound_n_with n new = strip_1qnt o
                   (Term.map_aterms (fn trm => if trm = Bound n then new else trm));
             in
              strip_atype @{term "\<And> state_rel field_num \<sigma> s.
               corres state_rel e (e' x') \<xi> ((\<gamma>!x) # \<gamma>) \<Xi>'
               (Some (TRecord (typ[field_num := (fst (typ ! field_num), fst (snd (typ ! field_num)), Present)]) (Boxed Writable ptrl)) # \<Gamma>e) \<sigma> s"}
               |> rep_Bound_n_with 3 state_rel |> rep_Bound_n_with 2 isa_int
             end;
  val prms = map (HOLogic.mk_Trueprop o strip_atype)
            [ass1, ass2, ass3, ass4, ass5, ass6, ass7, ass8] @ [ass9];
>>>>>>> origin/dargenttyping
*)

fun put_let_put_default_mk_prog term (heap :  HeapLiftBase.heap_info) struct_ty 
   (nth_field : HeapLiftBase.field_info) 
 :  term  =
  let
 

  val field_setter        = #setter nth_field;

  val is_valid_struct = Typtab.lookup (#heap_valid_getters heap) struct_ty
                       |> Utils.the' "is_valid_struct in put_let_put_default_mk_prog failed." |> Const;
  val heap_struct_update = Typtab.lookup (#heap_setters heap) struct_ty
                         |> Utils.the' "heap_struct_update in put_let_put_default_mk_prog failed."
                         |> Const;

  val term = strip_atype term $ is_valid_struct $ heap_struct_update $ field_setter
  in 
    term
 end


fun take_member_default_mk_prog term (heap : HeapLiftBase.heap_info) struct_ty 
   (nth_field : HeapLiftBase.field_info) 
 :  term  =
  let  

   val field_getter    = #getter nth_field;

   val is_valid_struct = Typtab.lookup (#heap_valid_getters heap) struct_ty
             |> Utils.the' "is_valid_struct in take_member_default_mk_prog failed."
             |> Const;
   val heap_getter = Typtab.lookup (#heap_getters heap) struct_ty
             |> Utils.the' "heap_getter in take_member_default_mk_prog failed." |> Const
       
   val term = strip_atype  term 
              $ is_valid_struct $ field_getter $ heap_getter                       

  in
     term
  end

val put_default_mk_prog = put_let_put_default_mk_prog put_default_prog
val let_put_default_mk_prog = put_let_put_default_mk_prog let_put_default_prog

val member_default_mk_prog = take_member_default_mk_prog member_default_prog

fun take_default_mk_prog Unboxed = 
   (fn _  => fn _ => 
      fn (nth_field : HeapLiftBase.field_info) =>
      (take_unboxed_default_prog $  #getter nth_field) )
  | take_default_mk_prog (Boxed(Writable, _)) =  take_member_default_mk_prog take_boxed_default_prog
  | take_default_mk_prog _  = error "in take_default_mk_prog failed."

\<close>

(* Now, custom layouts *)


ML \<open>
fun put_let_put_custom_mk_prog  
    (file_nm : string) term
    (_ : FunctionInfo.function_info)
    (layout : field_layout)
     ctxt : term =
let 
  val custom_setter = # setter layout  (* TODO recupper ler terme *)
  val setter_info = get_fun_info file_nm custom_setter ctxt
  val custom_isa_setter = # const setter_info
in
  term $ custom_isa_setter
end

fun take_member_custom_mk_prog term 
    (getter_info :  FunctionInfo.function_info)
    (_ : field_layout)
    (_ : Proof.context) : term  =
let 
  val custom_isa_getter = # const getter_info
in
   term $ custom_isa_getter
end 

fun put_custom_mk_prog file_nm = put_let_put_custom_mk_prog file_nm put_custom_prog
fun let_put_custom_mk_prog file_nm = put_let_put_custom_mk_prog file_nm let_put_custom_prog

val take_custom_mk_prog = take_member_custom_mk_prog take_custom_prog
val member_custom_mk_prog = take_member_custom_mk_prog member_custom_prog
\<close>




(* Now generic functions *)

ML \<open>

fun mk_specialised_corres_default 
  (mk_term : HeapLiftBase.heap_info -> Typtab.key -> HeapLiftBase.field_info -> term)
  
  (field_num:int) uval (file_nm : string)  
  ctxt =
  let     
    val struct_C_nm     = get_ty_nm_C uval;
    val heap            = Symtab.lookup (HeapInfo.get (Proof_Context.theory_of ctxt)) file_nm
                        |> Utils.the' "heap in mk_specialised_corres_default failed."
                        |> #heap_info;
    val field_info      = Symtab.lookup (#structs heap) struct_C_nm
                        |> Utils.the' "field_info in mk_specialised_corres_default failed."
                        |> #field_info;
    val nth_field       = List.nth (field_info, field_num);
    val struct_ty       = Syntax.read_typ ctxt struct_C_nm;
  
    val term = mk_term heap struct_ty nth_field
    val field_ty            = #field_type nth_field; 
    val total_num = List.length field_info   
  in
   (total_num, term, field_ty)
  end
\<close>


ML \<open>

fun mk_specialised_corres_custom   
  (mk_term : FunctionInfo.function_info -> field_layout -> Proof.context -> term)  
  (field_num:int)  (layouts : field_layout list) (file_nm : string)  
  ctxt =
   let
    val layout = List.nth (layouts , field_num) 
    val custom_getter = # getter layout 
    val getter_info = get_fun_info file_nm custom_getter ctxt
    val field_ty = # return_type getter_info
    
    val term = (mk_term getter_info layout ctxt)    
    val total_num = List.length layouts    
  in
    (total_num, term, field_ty)
  end
\<close>

ML \<open>

fun mk_specialised_corres_generic 
  (mk_term_default : HeapLiftBase.heap_info -> Typtab.key -> HeapLiftBase.field_info -> term)
 (mk_term_custom : FunctionInfo.function_info -> field_layout -> Proof.context -> term)  
  (mk_lemma : int -> field_layout uval -> int * term * typ -> Proof.context -> term)
  (field_num:int) uval (file_nm : string) 
  ctxt =
 let
   val args =
  case get_sigil_layout (get_uval_sigil uval) of
     DefaultLayout => 
       mk_specialised_corres_default
        mk_term_default
         field_num uval file_nm ctxt
        
    | CustomLayout l => 
        mk_specialised_corres_custom mk_term_custom field_num l file_nm ctxt 
  in
   mk_lemma field_num uval args ctxt
end
 
\<close>




ML \<open>
fun mk_specialised_corres_put (field_num:int) uval (file_nm : string) ctxt : term =
  let
    val term = mk_specialised_corres_generic 
       put_default_mk_prog (put_custom_mk_prog file_nm)
       mk_specialised_corres_put_aux 
        field_num uval file_nm ctxt
    val _ = tracing ("    finished mk_spec_corres_put for struct " ^ (get_uval_name uval) ^ " " ^
          Int.toString field_num);
  in
   term  
  end

fun mk_specialised_corres_let_put (field_num:int) uval (file_nm : string) ctxt : term =
  let
    val term = mk_specialised_corres_generic 
       let_put_default_mk_prog (let_put_custom_mk_prog file_nm)
       mk_specialised_corres_let_put_aux 
        field_num uval file_nm ctxt
    val _ = tracing ("    finished mk_spec_corres_let_put for struct " ^ (get_uval_name uval) ^ " " ^
          Int.toString field_num);
  in
   term  
  end
fun mk_specialised_corres_take (field_num:int) uval (file_nm : string) ctxt : term =
  let
    val term = mk_specialised_corres_generic 
       (take_default_mk_prog (get_uval_sigil uval)) take_custom_mk_prog
       mk_specialised_corres_take_aux 
        field_num uval file_nm ctxt
    val _ = tracing ("    finished mk_spec_corres_take for struct " ^ (get_uval_name uval) ^ " " ^
          Int.toString field_num);
  in
   term  
  end

fun mk_specialised_corres_member (field_num:int) uval (file_nm : string) ctxt : term =
  let
    val term = mk_specialised_corres_generic 
       member_default_mk_prog member_custom_mk_prog
       mk_specialised_corres_member_aux 
        field_num uval file_nm ctxt
    val _ = tracing ("    finished mk_spec_corres_member for struct " ^ (get_uval_name uval) ^ " " ^
          Int.toString field_num);
  in
   term  
  end
(*
<<<<<<< HEAD
=======
  (* define meta-assumptions in specialised corres lemmas.*)
  val ass1 = @{term "\<Gamma>' ! x = Some (TRecord typ (Boxed ReadOnly ptrl))"} ;
  val ass3 = @{term "\<lambda> x'. val_rel (\<gamma>!x) x'"} $ (Free ("x'", ty));
  val ass4 = @{term "\<lambda> ty. type_rel (type_repr (TRecord typ (Boxed ReadOnly ptrl))) ty"}
             $ (Const ("Pure.type", Term.itselfT ty));
  val ass5 = @{term "\<lambda> ty isa_field_num. type_rel (type_repr (fst (snd (typ ! isa_field_num)))) ty"}
             $ (Const ("Pure.type", Term.itselfT field_ty)) $ isa_field_num;
  val ass6 = @{term "\<lambda> isa_field_num . \<Xi>', 0, [], {}, \<Gamma>' \<turnstile> Member (Var x) isa_field_num : te"} $ isa_field_num;
  val ass7 = @{term " \<Xi>', 0, [], {}, \<Gamma>' \<turnstile> Var x : TRecord typ (Boxed ReadOnly ptrl)"};
  val prms = map (HOLogic.mk_Trueprop o strip_atype) [ass1, ass3, ass4, ass5, ass6, ass7];

  (* define the conclusion of the lemma.*)
  val cncl_body =
       let
         val is_valid_struct = Typtab.lookup (#heap_valid_getters heap) struct_ty
            |> Utils.the' "is_valid_struct in mk_specialised_corres_member failed."
            |> Const;
         val heap_getter = Typtab.lookup (#heap_getters heap) struct_ty
            |> Utils.the' "heap_getter in mk_specialised_corres_member failed."
            |> Const;
       in
       @{term "\<lambda> state_rel is_valid getter heap field_num field_getter.
         corres
          state_rel
          (Member (Var x) field_num)
          (do _ \<leftarrow> guard (\<lambda>s. is_valid s x');
              gets (\<lambda>s. field_getter (heap s x')) od)
           \<xi>' \<gamma> \<Xi>' \<Gamma>' \<sigma> s"} $
        state_rel $ is_valid_struct $ field_getter $ heap_getter $ isa_field_num $ field_getter
        |> strip_atype
        |> HOLogic.mk_Trueprop
       end;
  val cncl =
   case ml_sigil of
      Writable => cncl_body
    | ReadOnly => cncl_body
    | _ => error "Member is supported for Read_Only only.";
  val member_term = mk_meta_imps prms cncl ctxt |> Syntax.check_term ctxt;
  val _ = tracing ("    finished mk_spec_corres_member for struct " ^ get_uval_name uval ^ " " ^
   Int.toString field_num);
 in member_term end;
>>>>>>> origin/dargenttyping
*)
\<close>


ML\<open> fun mk_urecord_lems_for_uval file_nm ctxt (uval:field_layout uval) =
(* specialised-lemma generation for nth struct.*)
(* All uvals can reach this function. I have to filter them at some point.*)
 let
  val thy = Proof_Context.theory_of ctxt;
  val ml_sigil    = get_uval_sigil uval;
  val struct_C_nm = get_ty_nm_C uval;
  val _ = tracing ("mk_urecord_lems_for_uval is generating lems for " ^ struct_C_nm)
  
  
  val (num_of_fields, field_names) = 
    case get_sigil_layout ml_sigil of
      DefaultLayout =>
        let
          val heap = Symtab.lookup (HeapInfo.get thy) file_nm
              |> Option.map #heap_info;
          fun get_structs heap = Symtab.lookup (#structs heap) struct_C_nm : 'a option;

          val field_info = heap ?> get_structs +> #field_info |> these;
        in
          (List.length field_info, List.map #name field_info)
        end
    | CustomLayout l => (List.length l, List.map #name l)

  (* specialised_lemmas for each fields.
   * Three lemmas are generated if uval is of Writable.*)
  fun mk_lems_for_nth_field (field_num:int) =
   let
    val lem_tys =
      case ml_sigil of
          Boxed(Writable, _) => [TakeBoxed, PutBoxed, LetPutBoxed]
        | Unboxed  => [TakeUnboxed]
        | Boxed(ReadOnly, _) => [MemberReadOnly];
    val field_C_nm           = List.nth (field_names, field_num)
    fun get_sigil_nm sigil   = case sigil of
          Boxed(Writable, _) => "writable"
        | Unboxed  => "unboxed"
        | Boxed(ReadOnly, _) => "readonly"
    fun mk_lem_nm st         = st ^ struct_C_nm ^ "_" ^ field_C_nm ^ "_" ^ get_sigil_nm ml_sigil;
    fun get_corres_nm lem_ty = case lem_ty of
          TakeBoxed      => mk_lem_nm "corres_take_"
        | TakeUnboxed    => mk_lem_nm "corres_take_ub_"
        | PutBoxed       => mk_lem_nm "corres_put_"
        | LetPutBoxed    => mk_lem_nm "corres_let_put_"
        | MemberReadOnly => mk_lem_nm "corres_member_"
        | _ => error "not supported lem_ty"
    fun get_prop lem_ty =
      case lem_ty of
          TakeBoxed      => mk_specialised_corres_take   field_num uval file_nm ctxt
        | TakeUnboxed    => mk_specialised_corres_take   field_num uval file_nm ctxt
        | PutBoxed       => mk_specialised_corres_put    field_num uval file_nm ctxt
        | LetPutBoxed    => mk_specialised_corres_let_put field_num uval file_nm ctxt
        | MemberReadOnly => mk_specialised_corres_member field_num uval file_nm ctxt
        | _  => error "get_prop failed. For now I only support TakeBoxed, TakeUnboxed, PutBoxed, MemberBoxed, and MemberReadOnly.";
     fun get_tac (lem_ty:bucket) =
      case lem_ty of
          (* FIXME: *)
          TakeBoxed      => (fn ctxt : Proof.context => if true then corres_take_boxed_tac ctxt else Skip_Proof.cheat_tac ctxt):(Proof.context -> int -> tactic)
        | TakeUnboxed    => (fn ctxt : Proof.context => if true then K (corres_take_unboxed_tac ctxt) else Skip_Proof.cheat_tac ctxt):(Proof.context -> int -> tactic)
        | PutBoxed       => (fn ctxt : Proof.context => if true then corres_put_boxed_tac ctxt else Skip_Proof.cheat_tac ctxt):(Proof.context -> int -> tactic)
        | LetPutBoxed    => (fn ctxt : Proof.context => if true then corres_let_put_boxed_tac ctxt else Skip_Proof.cheat_tac ctxt):(Proof.context -> int -> tactic)
        | MemberReadOnly => (fn ctxt : Proof.context => if true then corres_take_boxed_tac ctxt else Skip_Proof.cheat_tac ctxt):(Proof.context -> int -> tactic)
        | _ => error "get_tac failed. For now I only support TakeBoxed, TakeUnboxed, PutBoxed, MemberBoxed, and MemberReadOnly.";
    fun get_lem lem_ty =
      { name      = get_corres_nm lem_ty,
        bucket    = lem_ty,
        prop      = get_prop lem_ty,
        mk_tactic = fn ctxt => (get_tac lem_ty) ctxt 1};
    (* Probably, I can filter the list of uvals here.*)
    (* I have to decide which lem I should avoid to generate based on sigils and autocorres' ouptut.. *)
    (* I have uval, so I can use ac_mk_struct_info_for and ac_mk_heap_getters_for to make the decision.*)
    fun check_ac_output_for lem_ty = case lem_ty of
       TakeBoxed =>      ac_mk_heap_getters_for file_nm thy struct_C_nm
     | TakeUnboxed =>    ac_mk_struct_info_for  file_nm thy uval
     | PutBoxed =>       ac_mk_heap_getters_for file_nm thy struct_C_nm
     | LetPutBoxed =>    ac_mk_heap_getters_for file_nm thy struct_C_nm
     | MemberReadOnly => ac_mk_heap_getters_for file_nm thy struct_C_nm
     | _ => error "check_ac_ouput in mk_lems_for_nth_field failed. This lem_ty is not supported."
    val lem_tys_for_generation = filter (check_ac_output_for) lem_tys;
    val lems_for_nth_field = List.map get_lem lem_tys_for_generation: lem list;
   in
    lems_for_nth_field : lem list
   end;

  val urecord_lems_for_nth_struct = List.tabulate (num_of_fields, fn field_num =>
    let
     val _ = tracing ("  started working on field number " ^ (Int.toString field_num))
    in
     mk_lems_for_nth_field field_num end) |> List.concat : lem list;

 in
  urecord_lems_for_nth_struct : lem list
 end;
\<close>

end

end
