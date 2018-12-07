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

theory Specialised_Lemma_USum
imports
  Read_Table
  SpecialisedLemmaTactic
begin

context update_sem_init
begin

ML{* (* get_castable_uvals_from *)
local

infix can_be_casted_to
fun (uval1 can_be_casted_to uval2) ctxt heap_info =
(* Returns NONE if uval1 cannot be casted to uval2.*)
(* Returns (SOME int) if uval1 can be casted to uval2 and we lose the int-th field in the c-struct for
 uval1 by copying uval1 to uval2.*)
(* TODO: improve! *)
 let
  infix might_be_casted_to;

  fun (xs might_be_casted_to ys) = (ys is_smaller_than_by_one xs) andalso (ys is_subset_of xs);
  fun uval_to_field_names uval = heap_info_uval_to_field_names heap_info uval;
  fun uval_to_field_types uval = heap_info_uval_to_field_types heap_info uval;
  val field_names1 = uval_to_field_names uval1;
  val field_names2 = uval_to_field_names uval2;
  val field_types1 = uval_to_field_types uval1;
  val field_types2 = uval_to_field_types uval2;
  val test1 = (field_names1 might_be_casted_to field_names2);
  val test2 = (field_types1 might_be_casted_to field_types2);
  val test3 = (usum_list_of_types ctxt uval1 might_be_casted_to usum_list_of_types ctxt uval2);
  fun are_same_pairs xs ys = ListPair.all (fn (x,y) => x = y) (xs, ys);
  val test = if (test1 andalso test2 andalso test3)
             then
              let val nth_is_missing = which_is_missing field_names1 field_names2
              in are_same_pairs (remove_nth nth_is_missing field_names1) field_names2 andalso
                 are_same_pairs (remove_nth nth_is_missing field_types1) field_types2
              end
             else false;

  val some_missing_field_num =
      if test then which_is_missing field_names1 field_names2 |> SOME else NONE;
 in
  (some_missing_field_num : int option)
 end;

fun get_castable_uvals_from' _ _ (_:uval) []        = []
  | get_castable_uvals_from' ctxt heap (from:uval) (to::tos) =
   let val some_rmved_field_num  = (from can_be_casted_to to) ctxt heap;
       val some_pair = if is_some some_rmved_field_num
                       then SOME (the some_rmved_field_num, to) else NONE
   in some_pair :: get_castable_uvals_from' ctxt heap from tos
   end;

in

fun get_castable_uvals_from ctxt heap from tos =
    get_castable_uvals_from' ctxt heap from (get_usums tos) |> get_somes

end;
*}


ML{* fun mk_case_prop from_uval to_uval field_num file_nm ctxt =
(* field_num is the number of the field that is being tested for matching.*)
 let
  val _ = tracing ("  started mk_case_prop for field_num " ^ string_of_int field_num)
  val from_struct_C_nm = get_ty_nm_C from_uval;
  val to_struct_C_nm   = get_ty_nm_C to_uval;
  val _ = tracing ("  casting from " ^ from_struct_C_nm ^ " to " ^ to_struct_C_nm)
  val heap = Symtab.lookup (HeapInfo.get (Proof_Context.theory_of ctxt)) file_nm
      |> Utils.the' "heap in mk_case_prop failed."
      |> #heap_info;
  val get_struct_info  = fn struct_C_nm => Symtab.lookup (heap |> #structs) struct_C_nm
      |> Utils.the' "get_struct_info in mk_prop in Specialised_Lemma_USum.thy failed.";
  val from_struct_info = get_struct_info from_struct_C_nm;
  val to_struct_info   = get_struct_info to_struct_C_nm;
  val from_field_info  = #field_info from_struct_info;
  val to_field_info    = #field_info to_struct_info;
  val nth_field_ml_tag_name = from_field_info |> (fn list => List.nth (list, field_num)) |> #name
                              |> cut_C;
  val nth_field_tag_name = nth_field_ml_tag_name |> Utils.encode_isa_string;
  val get_tag_names = fn uval => heap_info_uval_to_field_names heap uval |> tl |> map (unsuffix "_C");
  val from_tag_nms  = get_tag_names from_uval;
  val to_tag_nms    = get_tag_names to_uval;

  val alternative_tys = map (fn n => Free ("alt_ty" ^ string_of_int n, @{typ "Cogent.type"}))
    (1 upto length from_tag_nms)
  val tag_ty_bits    = from_tag_nms ~~ alternative_tys
  val to_tag_ty_bits = to_tag_nms ~~ map (the o AList.lookup (op =) tag_ty_bits) to_tag_nms
  val from_sumT      = @{term TSum} $ HOLogic.mk_list @{typ "(string \<times> Cogent.type)"}
                       (map HOLogic.mk_prod (map (apfst HOLogic.mk_string) tag_ty_bits))
  val to_sumT        = @{term TSum} $ HOLogic.mk_list @{typ "(string \<times> Cogent.type)"}
                       (map HOLogic.mk_prod (map (apfst HOLogic.mk_string) to_tag_ty_bits))
  val dropped_bits   = filter (fn (s, _) => AList.lookup (op =) to_tag_ty_bits s = NONE) tag_ty_bits
  val taken_typ = case dropped_bits of [v] => snd v
    | _ => raise TERM ("dropped_bits: " ^ (@{make_string} (dropped_bits, tag_ty_bits, to_tag_ty_bits)), [])

  val from_tag_C = from_field_info |> hd |> #getter; (* tag_C is always the first element of struct.*)
  val corres     = Syntax.read_term ctxt "corres";
  val setters    = to_field_info |> map #setter;
  val getters    = from_field_info |> map #getter |> remove_nth field_num;

  (* Monadic C code in the conclusion.*)
  val monadic_c =
   let
    fun mk_set_get setter getter body =
     let
      val x'      = strip_type @{term "x'"};
      val getter' = Term.absdummy dummyT (getter $ x');
     in setter $ getter' $ body end;
    val copy = ListPair.foldl (uncurry_triple mk_set_get) (strip_type @{term "dummy"}) (setters, getters)
              |> Syntax.check_term ctxt;
    val TAG_ENUM = Syntax.read_term ctxt ("TAG_ENUM_" ^ nth_field_ml_tag_name);
    val match_tag_getter = List.nth (from_field_info, field_num) |> #getter;
   in
    @{term "\<lambda> copy from_tag_C TAG_ENUM match_tag_getter.
         (condition (\<lambda>_. from_tag_C x' = TAG_ENUM)
           (match' (match_tag_getter x'))
           (do x \<leftarrow> gets (\<lambda>_. copy); not_match' x od))"}
     $ copy $ from_tag_C $ TAG_ENUM $ match_tag_getter
   end;

  fun mk_ass2 tag_list    = @{mk_term "\<Gamma>' ! x = Some ?tag_list" tag_list} tag_list;
  fun mk_ass6 tag_list    = @{mk_term "\<Xi>', [], \<Gamma>1 \<turnstile> Var x : ?tag_list" tag_list} tag_list;
  fun mk_ass8 other_tags  = @{mk_term "\<Xi>', [], Some ?other_tags # \<Gamma>2 \<turnstile> not_match : t" other_tags} other_tags;
  fun mk_ass10 other_tags =
   @{mk_term "\<And>r r'. val_rel r r' \<Longrightarrow> ?corres srel not_match (not_match' r') \<xi>' (r # \<gamma>) \<Xi>'
    (Some (?other_tags) # \<Gamma>2) \<sigma> s" (corres, other_tags)} (corres, other_tags);

  val ass1 = @{term "x < length \<Gamma>'"};
  val ass2 = mk_ass2 from_sumT;
  val ass3 = @{term "[] \<turnstile> \<Gamma>' \<leadsto> \<Gamma>1 | \<Gamma>2"};
  val ass4 = @{term "val_rel (\<gamma> ! x) x'"};
  val ass6 = mk_ass6 from_sumT
  val ass7 = @{term "\<lambda>taken_typ. \<Xi>', [], Some taken_typ # \<Gamma>2 \<turnstile> match : t"} $ taken_typ;
  val ass8 = mk_ass8 to_sumT;
  val ass9 = @{mk_term "\<And>a a'. val_rel a a' \<Longrightarrow>
   ?corres srel match (match' a') \<xi>' (a # \<gamma>) \<Xi>' (Some ?match_typ # \<Gamma>2) \<sigma> s"(corres, match_typ)}
    (corres, taken_typ);
  val ass10= mk_ass10 to_sumT;
  val prms = map (HOLogic.mk_Trueprop o strip_atype)
     [ass1, ass2, ass3, ass4, ass6, ass7, ass8] @ [ass9, ass10];

  val cncl = @{mk_term
          "?corres srel (Case (Var x) ?nth_field_tag_name match not_match) ?monadic_c \<xi>' \<gamma> \<Xi>' \<Gamma>' \<sigma> s"
          (corres, nth_field_tag_name, monadic_c)} (corres, nth_field_tag_name, monadic_c)
          |> HOLogic.mk_Trueprop;

in
  mk_meta_imps prms cncl ctxt |> Syntax.check_term ctxt
end
*}

ML{* (* mk_case_lem_for_uval *)
local

fun mk_case_lem_from_to (from:uval) field_num (to:uval) file_nm ctxt  =
{ name = "corres_case_" ^ get_uval_name from ^ "_" ^ Int.toString field_num ^ "th_field",
  bucket = Case,
  prop = mk_case_prop from to field_num file_nm ctxt,
  mk_tactic = if true then (fn ctxt => corres_case_tac ctxt 1) else K (Skip_Proof.cheat_tac ctxt 1) };

fun mk_case_lems_from_tos from (num_tos : (int * uval) list) file_nm ctxt = map
   (fn num_to => mk_case_lem_from_to from (fst num_to) (snd num_to) file_nm ctxt) num_tos

in

fun mk_case_lems_for_uval file_nm ctxt uvals from =
 let
  val heap_info = Symtab.lookup (HeapInfo.get (Proof_Context.theory_of ctxt)) file_nm
                 |> Utils.the' "the' in mk_specialised_case_lemmas_for_uval failed."
                 |> #heap_info;
  val num_tos   = get_castable_uvals_from ctxt heap_info from uvals;
  val lems      = mk_case_lems_from_tos from num_tos file_nm ctxt;
 in
  lems
 end;

end;
*}

ML{* (* local_setup_specialised_esacs *)
local

fun specialise_esac_thm ctxt trm =
 let
  val cterm_of    = Thm.cterm_of ctxt;
  val corres_esac = Proof_Context.get_thm ctxt "corres_esac";
  val vars        = Term.add_vars (Thm.prop_of corres_esac) [];
  (* get_val' is the 5th variable counting from 0.*)
  val get_val'    = List.nth (vars, 5);
  val my_esac     = Drule.infer_instantiate ctxt [(("get_val'", 0), cterm_of trm)] corres_esac (* TODO make sure 0 means what I think it means *)
 in my_esac end;

fun mk_specialised_esac_lemma file_nm ctxt from_usum =
 let
  val from_C_nm       = get_ty_nm_C from_usum;
  val _               = tracing ("  mk_specialised_esac_lemma for " ^ from_C_nm)
  val thy             = Proof_Context.theory_of ctxt;
  val is_usum         = get_usums [from_usum] |> null |> not;
  fun get_struct_info (hinfo : HeapLiftBase.heap_info)
                      = Symtab.lookup (#structs hinfo) from_C_nm;
  fun has_2elems list = List.length list = 2;
  val some_hinfo      = (Symtab.lookup (HeapInfo.get thy) file_nm) +> #heap_info;
  val some_sinfo      = some_hinfo ?> get_struct_info;
  val some_finfo      = some_sinfo +> #field_info;
  val has_2fields     = some_finfo +> has_2elems |> is_some_true;
  val is_esac         = is_usum andalso has_2fields;
  fun get_1st_elem list = List.nth (list, 1); (* counting from 0th.*)
  val some_fst_getter = some_finfo +> get_1st_elem +> #getter;
  val _               = if is_esac
                        then tracing ("  " ^ from_C_nm ^ " is for esac.")
                        else tracing ("  " ^ from_C_nm ^ " is not for esac.");
  val some_thm        = if is_esac
                        then some_fst_getter +> specialise_esac_thm ctxt
                        else NONE
 in some_thm end;

in

fun local_setup_specialised_esacs file_nm lthy =
 let
  val _      = tracing "started local_setup_specialised_esacs"
  val thy    = Proof_Context.theory_of lthy;
  val usums  = read_table file_nm thy
              |> get_usums
              |> get_uvals_for_which_ac_mk_st_info file_nm thy;
  fun mk_some_esac_lemma usum = mk_specialised_esac_lemma file_nm lthy usum;
  val esac_thms = List.mapPartial mk_some_esac_lemma usums;
  val lthy' = Local_Theory.notes [((Binding.name "corres_esacs", []), [(esac_thms, [])])] lthy |> snd
 in lthy' end;

end;
*}

end

end
