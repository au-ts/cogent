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

(* TODO: mk_specialised_corres_take and mk_specialised_corres_put have code-duplication
 *       Refactor it.*)
ML\<open> fun mk_specialised_corres_take (field_num:int) uval file_nm ctxt =
(* Generate specialised Take lemmas for the Writables and Unboxeds.*)
 let
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
                ReadOnly => @{term "Boxed ReadOnly undefined"}
              | Writable => @{term "Boxed Writable undefined"}
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
  (* define the conclusion of the lemma.*)
  (* Unboxed-Take and Boxed-Take have different conclusions.*)
  val cncl =
   case ml_sigil of
      Unboxed =>
       (strip_atype @{term "\<lambda> state_rel field_num getter .
         corres state_rel
           (Take (Var x) field_num e)
           (gets (\<lambda>s. getter x') >>= e') \<xi> \<gamma> \<Xi>' \<Gamma>' \<sigma> s"}) $
       state_rel $ isa_field_num $ field_getter |> HOLogic.mk_Trueprop
    | Writable =>
       let
         val is_valid_struct = Typtab.lookup (#heap_valid_getters heap) struct_ty
             |> Utils.the' "is_valid_struct in mk_specialised_corres_take failed."
             |> Const;
         val heap_getter = Typtab.lookup (#heap_getters heap) struct_ty
             |> Utils.the' "heap_getter in mk_specialised_corres_take failed." |> Const
       in
        strip_atype @{term "\<lambda> state_rel field_num is_valid getter heap .
         corres state_rel
          (Take (Var x) field_num e)
          (do _ \<leftarrow> guard (\<lambda>s. is_valid s x'); z \<leftarrow> gets (\<lambda>s. getter (heap s x')); e' z od)
           \<xi> \<gamma> \<Xi>' \<Gamma>' \<sigma> s"}
         $ state_rel $ isa_field_num $ is_valid_struct $ field_getter $ heap_getter
         |> HOLogic.mk_Trueprop
       end
    | ReadOnly => error "ReadOnly is not supported by cncl in mk_specialised_corres_take. :(";
  val take_term = mk_meta_imps prms cncl ctxt |> Syntax.check_term ctxt;
  val _ = tracing ("    finished mk_spec_corres_take for struct " ^ (get_uval_name uval) ^ " " ^  Int.toString field_num);
 in take_term
 end;
\<close>

ML\<open> fun mk_specialised_corres_put (field_num:int) uval file_nm ctxt =
(* Generate specialised Put lemmas.*)
 let
  (* define auxiliary values and functions.*)
  val struct_C_nm     = get_ty_nm_C uval;
  val struct_ty       = Syntax.read_typ ctxt struct_C_nm;
  val struct_C_ptr_ty = Syntax.read_typ ctxt (struct_C_nm ^ " ptr");
  val heap            = Symtab.lookup (HeapInfo.get (Proof_Context.theory_of ctxt)) file_nm
                       |> Utils.the' "heap in mk_specialised_corres_put failed."
                       |> #heap_info;
  val field_info = Symtab.lookup (heap |> #structs) struct_C_nm
                 |> Utils.the' "field_info in mk_specialised_corres_put failed."
                 |> #field_info;
  val nth_field           = List.nth (field_info, field_num);
  val field_ty            = #field_type nth_field;
  val isa_int             = encode_isa_int ctxt field_num;
  val isa_int_struct_leng = encode_isa_int ctxt (List.length field_info)
  fun get_clean_term str  = Syntax.read_term ctxt str |> strip_atype;
  val field_setter        = #setter nth_field;
  (* We could omit this explicit application of state_rel from this function by defining it before this line in ML.*)
  val state_rel           = get_clean_term "state_rel";

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

  (* auxiliary lemmas to define the conclusion.*)

  val is_valid_struct = Typtab.lookup (#heap_valid_getters heap) struct_ty
                       |> Utils.the' "is_valid_struct in mk_specialised_corres_put failed." |> Const;
  val heap_struct_update = Typtab.lookup (#heap_setters heap) struct_ty
                         |> Utils.the' "heap_struct_update in mk_specialised_corres_put failed."
                         |> Const;
  val cncl = (strip_atype @{term "\<lambda> state_rel field_num is_valid_struct heap_struct_update field_setter .
     corres state_rel
      (Put (Var x) field_num (Var v))
      (do
       ptr \<leftarrow> gets (\<lambda>_. x');
       _ \<leftarrow> guard (\<lambda>s. is_valid_struct s ptr);
       _ \<leftarrow> modify (heap_struct_update (\<lambda>a. a(ptr := field_setter (\<lambda>a. v') (a ptr))));
       gets (\<lambda>_. ptr)
       od) \<xi> \<gamma> \<Xi>' \<Gamma>' \<sigma> s"}) $
  (* We can omit this explicit application of state_rel from this function by defining it before this line in ML.*)
  state_rel $ isa_int $ is_valid_struct $ heap_struct_update $ field_setter |> HOLogic.mk_Trueprop;
  val put_term = mk_meta_imps prms cncl ctxt |> Syntax.check_term ctxt;
  val _ = tracing ("    finished mk_spec_corres_put for struct " ^ (get_uval_name uval) ^ " " ^
          Int.toString field_num);
 in put_term
 end;
\<close>

ML\<open> fun mk_specialised_corres_let_put (field_num:int) uval file_nm ctxt =
(* Generate specialised Let-Put lemmas.*)
 let
  (* define auxiliary values and functions.*)
  val struct_C_nm     = get_ty_nm_C uval;
  val struct_ty       = Syntax.read_typ ctxt struct_C_nm;
  val struct_C_ptr_ty = Syntax.read_typ ctxt (struct_C_nm ^ " ptr");
  val heap            = Symtab.lookup (HeapInfo.get (Proof_Context.theory_of ctxt)) file_nm
                       |> Utils.the' "heap in mk_specialised_corres_put failed."
                       |> #heap_info
  val field_info = Symtab.lookup (heap |> #structs) struct_C_nm
                 |> Utils.the' "field_info in mk_specialised_corres_put failed."
                 |> #field_info;
  val nth_field           = List.nth (field_info, field_num);
  val field_ty            = #field_type nth_field;
  val isa_int             = encode_isa_int ctxt field_num;
  val isa_int_struct_leng = encode_isa_int ctxt (List.length field_info)
  fun get_clean_term str  = Syntax.read_term ctxt str |> strip_atype;
  val field_setter        = #setter nth_field;
  (* We could omit this explicit application of state_rel from this function by defining it before this line in ML.*)
  val state_rel           = get_clean_term "state_rel";

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

  (* auxiliary lemmas to define the conclusion.*)

  val is_valid_struct = Typtab.lookup (#heap_valid_getters heap) struct_ty
                       |> Utils.the' "is_valid_struct in mk_specialised_corres_put failed." |> Const;
  val heap_struct_update = Typtab.lookup (#heap_setters heap) struct_ty
                         |> Utils.the' "heap_struct_update in mk_specialised_corres_put failed."
                         |> Const;
  val cncl = (strip_atype @{term "\<lambda> state_rel field_num is_valid_struct heap_struct_update field_setter .
     corres state_rel
      (expr.Let (Put (Var x) field_num (Var v)) e)
      (do
       ptr \<leftarrow> gets (\<lambda>_. x');
       _ \<leftarrow> guard (\<lambda>s. is_valid_struct s ptr);
       _ \<leftarrow> modify (heap_struct_update (\<lambda>a. a(ptr := field_setter (\<lambda>a. v') (a ptr))));
       ptr' \<leftarrow> gets (\<lambda>_. ptr);
       e' ptr'
       od) \<xi> \<gamma> \<Xi>' \<Gamma>' \<sigma> s"}) $
  (* We can omit this explicit application of state_rel from this function by defining it before this line in ML.*)
  state_rel $ isa_int $ is_valid_struct $ heap_struct_update $ field_setter |> HOLogic.mk_Trueprop;
  val put_term = mk_meta_imps prms cncl ctxt |> Syntax.check_term ctxt;
  val _ = tracing ("    finished mk_spec_corres_let_put for struct " ^ (get_uval_name uval) ^ " " ^
          Int.toString field_num);
 in  put_term
 end;
\<close>

ML\<open> fun mk_specialised_corres_member (field_num:int) uval file_nm ctxt =
(* Generate specialised lemmas for Member.*)
 let
  (* define auxiliary values and functions.*)
  val struct_C_nm     = get_ty_nm_C uval;
  val struct_ty       = Syntax.read_typ ctxt struct_C_nm;
  val struct_C_ptr_ty = Syntax.read_typ ctxt (struct_C_nm ^ " ptr");
  val isa_field_num   = encode_isa_int ctxt field_num;
  val heap            = Symtab.lookup (HeapInfo.get (Proof_Context.theory_of ctxt)) file_nm
                       |> Utils.the' "heap in mk_specialised_corres_member failed."
                       |> #heap_info
  val field_info      = Symtab.lookup (#structs heap) struct_C_nm
                       |> Utils.the' "field_info in mk_specialised_corres_member failed."
                       |> #field_info;
  val nth_field    = List.nth (field_info, field_num);
  val field_ty     = #field_type nth_field;
  val ml_sigil     = get_uval_sigil uval;
  val ty = case ml_sigil of
            Writable => struct_C_ptr_ty
          | ReadOnly => struct_C_ptr_ty
          | _ => error "ty in mk_specialised_corres_member failed.";
  val state_rel    = Syntax.read_term ctxt "state_rel";
  val field_getter = #getter nth_field;
  val ml_sigil     = get_uval_sigil uval;

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
\<close>

ML\<open> fun mk_urecord_lems_for_uval file_nm ctxt (uval:uval) =
(* specialised-lemma generation for nth struct.*)
(* All uvals can reach this function. I have to filter them at some point.*)
 let
  val thy = Proof_Context.theory_of ctxt;
  val ml_sigil    = get_uval_sigil uval;
  val struct_C_nm = get_ty_nm_C uval;
  val _ = tracing ("mk_urecord_lems_for_uval is generating lems for " ^ struct_C_nm)
  val heap = Symtab.lookup (HeapInfo.get thy) file_nm
              |> Option.map #heap_info;
  fun get_structs heap = Symtab.lookup (#structs heap) struct_C_nm : 'a option;
  val field_info = heap ?> get_structs +> #field_info |> these;
  val num_of_fields = List.length field_info;

  (* specialised_lemmas for each fields.
   * Three lemmas are generated if uval is of Writable.*)
  fun mk_lems_for_nth_field (field_num:int) =
   let
    val lem_tys =
      case ml_sigil of
          Writable => [TakeBoxed, PutBoxed, LetPutBoxed, MemberReadOnly]
        | Unboxed  => [TakeUnboxed]
        | ReadOnly => [MemberReadOnly];
    val field_C_nm           = List.nth (field_info, field_num) |> #name;
    fun get_sigil_nm sigil   = case sigil of
          Writable => "writable"
        | Unboxed  => "unboxed"
        | ReadOnly => "readonly"
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
