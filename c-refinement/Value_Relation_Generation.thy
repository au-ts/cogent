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

theory Value_Relation_Generation
imports
  "Cogent_Corres"
  "Specialised_Lemma_Utils"
begin

ML\<open> (* val_rel_def *)
local

fun mk_rhs_pro _ (field_info:HeapLiftBase.field_info list) =
(* val_rel generation for UProduct *)
 let
  val getters = map #getter field_info;
  val p1 = nth getters 0;
  val p2 = nth getters 1;
 in
 @{term "\<lambda> p1_C p2_C . (\<exists> p1 p2 .
   (uv = UProduct p1 p2) \<and>
    val_rel p1 (p1_C x) \<and>
    val_rel p2 (p2_C x))"} $ p1 $ p2
 end;

fun mk_rhs_rec _ (field_info:HeapLiftBase.field_info list) =
 (* val_rel generation for URecord *)
 let
  fun mk_nth_conjct n getter = @{term "val_rel"} $ (Const ("Product_Type.prod.fst", dummyT) $ Bound n) $ (getter $ @{term "x"}) |> strip_type;

  fun mk_conjcts' _ [] = []
   |  mk_conjcts' n (g::gs) = mk_nth_conjct n g :: mk_conjcts' (n - 1) gs;
  fun mk_conjcts getters = mk_conjcts' (length getters - 1) getters |> mk_HOL_conjs;

  fun mk_Bound_list 0 = Const ("List.list.Nil", dummyT)
   |  mk_Bound_list n = Const ("List.list.Cons", dummyT) $ Bound (n-1) $ mk_Bound_list (n-1);

  fun mk_fst_conjct n =
   Const ("HOL.eq",dummyT) $ Free ("uv", dummyT) $
   (Const ("UpdateSemantics.uval.URecord", dummyT) $ mk_Bound_list n);
 in
  mk_exists (get_field_names field_info)
  (HOLogic.mk_conj
   (field_info |> List.length |> mk_fst_conjct, field_info |> get_getters |> mk_conjcts))
 end;

fun mk_rhs_sum ctxt (field_info:HeapLiftBase.field_info list) =
 (* val_rel generation for USum *)
 let
  val getters = map #getter field_info;
  fun mk_one_disjunct ctxt tag_C getter =
   @{term "\<lambda> spec_tag_C spec_tag_isa_string spec_tag_const gen_tag_C tag uval .
    (tag = spec_tag_isa_string \<and>
     gen_tag_C x = spec_tag_const \<and>
     val_rel uval (spec_tag_C x))"}
    $ getter
    $(getter |> get_name |> Long_Name.base_name |> cut_C |> Utils.encode_isa_string)
    $(getter |> get_name |> Long_Name.base_name |> cut_C |> (fn tag_nm => "TAG_ENUM_" ^ tag_nm)
      |> Syntax.read_term ctxt)
    $(tag_C |> get_name |> Syntax.read_term ctxt);
  fun mk_list_of_disjuncts ctxt getters =
   map (strip_abs_body o clean_check_typ_of ctxt o mk_one_disjunct ctxt (hd getters)) (tl getters);
 in
  (* FIXME: construct correct repr *)
  @{mk_term "\<exists>repr tag uval. uv = UpdateSemantics.uval.USum tag uval repr \<and> ?eq" (eq)}
     (* NB: ?eq implicitly uses tag and uval as Bound 1 and Bound 0 *)
     (mk_HOL_disjs (mk_list_of_disjuncts ctxt getters))
 end;

val mk_rhs_abs = @{term "\<exists>abs. uv = UAbstract abs"} |> strip_atype;
(* val_rel generation for UAbstract *)

fun gen_mk_rhs ctxt file_name uval =
 let
  val thy = Proof_Context.theory_of ctxt;
  fun field_info ty = get_field_info (get_struct_info thy file_name) ty;
 in
  case uval of
    USum (ty_name  , _) => mk_rhs_sum ctxt (field_info ty_name)
  | UProduct ty_name    => mk_rhs_pro ctxt (field_info ty_name)
  | URecord (ty_name,_) => mk_rhs_rec ctxt (field_info ty_name)
  | UAbstract _         => mk_rhs_abs
 end;

in

fun val_rel_def file_name uval ctxt =
 let
  val ty_name = get_uval_name uval;
  val c_type  = Syntax.read_typ ctxt (ty_name ^ "_C");
  val lhs = @{term "val_rel"} $ Free ("uv", dummyT) $ Free("x",c_type);
  val rhs = gen_mk_rhs ctxt file_name uval;
  val equ = mk_eq_tm lhs rhs ctxt;
  val val_rel_name = "val_rel_" ^ ty_name ^"_C_def";
  val spec_def     = Specification.definition NONE [] [] ((Binding.name (val_rel_name), []), equ) ctxt;
  val thm     = spec_def |> fst |> snd |> snd;
  val lthy    = snd spec_def;
  val lthy'   = ValRelSimp.add_local thm lthy;
  val _ = tracing ("generating val_rel for " ^ (get_uval_name uval))
 in lthy' end;

end;
\<close>

ML\<open> fun guess_val_rel_type thm = case Thm.prop_of thm of
       Const ("Pure.eq", _) $ (val_rel $ uv $ x) $ rhs =>
         (case type_of x of
             Type (c_typ, _) => String.tokens (fn x => x = #".") c_typ
                                |> filter (String.isSuffix "_C") |> take 1
           | _ => [])
     | _ => []
\<close>

end
