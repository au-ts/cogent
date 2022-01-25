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

theory Utils
imports
  "AutoCorres.AutoCorres"
keywords "foobar_prove" :: thy_goal (* from Cookbook.*)
begin

text\<open> This theory file contains utility functions that are not specific to the trustworthy file
 system project. \<close>

text\<open> basics \<close>

ML\<open> fun uncurry_triple f (x, y, z) = f x y z; \<close>

text\<open> Operations on string.\<close>

ML\<open> fun cut_C str_C = unsuffix "_C" str_C;\<close>

ML\<open> (*rm_redundancy [1,2,3,4,2,3] = [1,2,3,4]*)
fun rm_redundancy [] = []
  | rm_redundancy (x::xs) = x::(rm_redundancy (List.filter (fn y => y <> x) xs));
\<close>

ML\<open> (*rm_redundancy [1,2,3,4,2,3] = [1,2,3,4]*)
fun rm_redundancy_by f [] = []
  | rm_redundancy_by f (x::xs) = x::(rm_redundancy_by f (List.filter (fn y => f y <> f x) xs));
\<close>


ML\<open> fun get_somes xs = xs
     |> filter (fn x => case x of NONE => false | _ => true)
     |> map (Utils.the' "get_somes failed");\<close>

ML\<open> fun remove_nth n xs =
(*  (counts from 0)*)
let
 fun remove_nth'  0 []      = error "cannot remove anything from an empty list."
   | remove_nth'  0 (_::xs) = xs
   | remove_nth'  _ []      = error "cannot remove anything from an empty list."
   | remove_nth'  n (x::xs) = x :: remove_nth'  (n - 1) xs
 in
 if n < 0 then error "n is smaller than 0" else remove_nth' n xs
end;

(* test *)
remove_nth 3 [0,1,2,3,4,5] = [0,1,2,4,5];
\<close>

ML\<open> fun nth_is_missing nth froms tos =
 let
  val nth_elem = List.nth (froms, nth);
  val test = List.find (fn to => nth_elem = to) tos |> is_none
 in test end;
\<close>

ML\<open> fun which_is_missing froms tos =
(* counts from 0*)
(* TODO: this does not work well if multiple elements are missing.
  But for our purpose, this is fine. Future work.*)
let
 fun which_is_missing' 0 _     _   = error "which_is_missing' failed. Nothing is missing"
   | which_is_missing' n froms tos =
      if   nth_is_missing n froms tos
      then n
      else which_is_missing' (n - 1) froms tos;
in
 which_is_missing' (List.length froms - 1) froms tos
end;
(* TODO: more exceptions. for negative n.*)

(* test *)
which_is_missing [2,4,6,1,2,5,4,3] [1,2,3,4,5];
\<close>

(* FIXME: These functions probably exist in library.ML. Remove code-duplication!*)
ML\<open> infix is_in
fun (x is_in ys) = List.find (fn y => x = y) ys |> is_some;
(* test *)
(4 is_in [1,2,3,4,5]) = true;
(9 is_in [1,2,3,4,5]) = false;
\<close>

ML\<open> infix is_subset_of
fun (xs is_subset_of ys) = List.all (fn x => x is_in ys) xs;
(* test *)
([4,3] is_subset_of [1,2,3,4,5]) = true;
([4,6,1,2,5,4,3] is_subset_of [1,2,3,4,5]) = false;
([1,2,3,4,5] is_subset_of [4,6,1,2,5,4,3]) = true;
\<close>

ML\<open> infix is_superset_of
fun (xs is_superset_of ys) = List.all (fn y => y is_in xs) ys;
(* test *)
([4,3] is_superset_of [1,2,3,4,5]) = false;
([4,6,1,2,5,4,3] is_superset_of [1,2,3,4,5]) = true;
([1,2,3,4,5] is_superset_of [4,6,1,2,5,4,3]) = false;
\<close>

ML\<open> infix is_smaller_than_by_one
fun (xs is_smaller_than_by_one ys) =
 let
(* why should I remove redundancy?
  val xs' = rm_redundancy xs;
  val ys' = rm_redundancy ys;
*)
 in
(*  List.length xs' + 1 = List.length ys' *)
  List.length xs + 1 = List.length ys
 end;

(* test *)
([4,5,3,2,4,1,2,3,4,5] is_smaller_than_by_one [4,6,1,2,5,3]) = true;
\<close>

text\<open> Operations on terms.\<close>

ML\<open> val strip_type = Term.map_types (K dummyT);\<close>

ML\<open> val strip_atype = Term.map_types (map_atyps (K dummyT)) \<close>

ML\<open> fun mk_Some thg = strip_atype @{term "\<lambda> thg . Some thg"} $ thg \<close>

ML\<open> fun clean_check_typ_of ctxt tm = tm
 |> strip_atype
 |> Syntax.check_term ctxt;
\<close>

ML\<open> fun clean_check_mkprop ctxt tm =
 clean_check_typ_of ctxt tm |> HOLogic.mk_Trueprop;
\<close>

ML\<open> (* mk_HOL_disjs makes nested disjunctions from a list of disjuncts.*)
fun mk_HOL_disjs tms = case tms of
 [] => error "The function mk_disjs should not be applied to an empty list."
|(tm::[]) => tm
|tms => HOLogic.mk_disj (hd tms, tms |> tl |> mk_HOL_disjs);

(* Test *)
mk_HOL_disjs [@{term "False"}, @{term "True"}, @{term "True"}] = @{term "False \<or> True \<or> True"}
\<close>

ML\<open> (* mk_HOL_conjs make nested conjunctions from a list of conjuncts*)
fun mk_HOL_conjs [] = error "error! The list of terms is empty."
 |  mk_HOL_conjs (tm::[]) = tm
 |  mk_HOL_conjs (tm::tms)= HOLogic.mk_conj (tm, mk_HOL_conjs tms);

(* Test *)
 mk_HOL_conjs [@{term "False"}, @{term "True"}, @{term "True"}] = @{term "False \<and> True \<and> True"}
\<close>

ML\<open> fun encode_isa_pair (fst,snd) = Const ("Product_Type.Pair", dummyT) $ fst $ snd; \<close>

ML\<open>
fun encode_isa_int (ctxt:Proof.context) int =
 Int.toString int |> Syntax.read_term ctxt |> strip_type;
\<close>

ML\<open> (* mk_isa_list takes a ml-list of isa-terms and returns isa-list of isa-terms.
 * Unlike Utils.encode_isa_list, mk_isa_list does not check types. *)
fun mk_isa_list [] = Const ("List.list.Nil", dummyT)
 |  mk_isa_list (x::xs:term list) = Const ("List.list.Cons", dummyT) $ x $ mk_isa_list xs;
\<close>

ML\<open> fun mk_eq_tm lhs rhs ctxt = Const ("Pure.eq", dummyT) $ lhs $ rhs |> clean_check_typ_of ctxt;\<close>

ML\<open> fun mk_meta_imps (prems:term list) (cncl:term) (ctxt:Proof.context) =
let
 fun mk_meta_imps' (prems:term list) (cncl:term) = case prems of
   [] => cncl
 | (prem::prems) => mk_meta_imps' prems (Logic.mk_implies (prem, cncl));
 val prop = mk_meta_imps' (List.rev prems) (cncl) |> clean_check_typ_of ctxt;
in prop end;
\<close>

ML\<open> (* strip_qnt strips terms of quantifiers.*)
fun strip_qnt (Const (_, _) $ Abs (_, _, t)) = strip_qnt t
 |  strip_qnt tm = tm
\<close>

ML\<open> (* strip_qnt strips terms of quantifiers.*)
fun strip_1qnt (Const (_, _) $ Abs (_, _, t)) = t
 |  strip_1qnt tm = tm
\<close>

(* Term.ML has a function similar to this. But we need the names to be "a", and
   I always want to use dummyT.*)
ML\<open> fun abs_dummy body = Abs ("a", dummyT, body); \<close>

ML\<open> val undefined = Const ("HOL.undefined", dummyT); \<close>

ML\<open> (* n_abs_dummy *)
local
  fun n_abs_dummy' 0 body = body
   |  n_abs_dummy' n body = abs_dummy (n_abs_dummy' (n - 1) body)
in
 fun n_abs_dummy n body =
  if n < 0 then error "n_abs_dummy failed. n is smaller than 0." else n_abs_dummy' n body;
end; \<close>

ML\<open> fun n_abs_undef n = n_abs_dummy n undefined; \<close>

ML\<open> fun apply_x_n_times_to_f x n f ctxt =
let
 fun apply_n_times 1 = f $ x
   | apply_n_times n = (apply_n_times (n - 1)) $ x
in
 if n < 1
 then error "apply_x_n_times_to_f faild. It no longer wants to apply x to f."
 else apply_n_times n |> strip_atype |> Syntax.check_term ctxt
end;

(* test *)
apply_x_n_times_to_f @{term "0"} 3 @{term "y"} @{context} = @{term "y 0 0 0"};
\<close>


ML\<open> (* update the type of a quantified variable.*)
(* Warning: this function is a little bit unreliable: it strips all the types in the body. *)
fun up_ty_of_qnt var_nm new_abs_qnt_ty ctxt trm =
 let
  fun up_ty_of_qnt' (Const (const_qnt_nm, const_qnt_ty) $ Abs (abs_qnt_nm, abs_qnt_ty, trm)) =
    if var_nm = abs_qnt_nm
    then (Const (const_qnt_nm, dummyT) $ Abs (abs_qnt_nm, new_abs_qnt_ty, strip_type trm))
    else (Const (const_qnt_nm, const_qnt_ty) $ Abs (abs_qnt_nm, abs_qnt_ty, up_ty_of_qnt' trm))
   |  up_ty_of_qnt' trm = trm;
 in
  up_ty_of_qnt' trm |> Syntax.check_term ctxt
 end;
\<close>

ML\<open> (* get_names takes a term and returns its name if it is well-defined.*)
fun get_name (Const (name, _)) = name
  | get_name (Free (name, _)) = name
  | get_name (Var ((name, _), _)) = name
  | get_name (Bound _) = error "Bound variables have no names."
  | get_name (Abs (name, _, _)) = name
  | get_name _ = error "get_name is not defined for function applications ($).";
\<close>

ML\<open> (* generate n-nested abstraction.*)
fun mk_exists [] body = body
 |  mk_exists (var_nm::var_nms) body =
     Const ("HOL.Ex", dummyT) $ Abs (var_nm, dummyT, mk_exists var_nms body);
\<close>

ML\<open> (* mk_meta_conjncts [thm1, thm2, thm3] = thm1 &&& thm2 &&& thm3. *)
fun mk_meta_conjncts [] = error "cannot make meta conjunctions."
 |  mk_meta_conjncts (thm::[]) = thm
 |  mk_meta_conjncts (thm::thms) = Conjunction.intr thm (mk_meta_conjncts thms)\<close>

ML\<open> (* add_simps adds simplification-rules into a given context. *)
fun add_simps [] ctxt = ctxt
 |  add_simps (thm::thms) ctxt = add_simps thms (Simplifier.add_simp thm ctxt)
\<close>

text\<open> Option.\<close>

ML\<open> infix 1 ?> ??> +>;
(* ?> is just >>= for option, I use the different symbol. *)
fun ((x:'a option) ?>  (f:'a -> 'b option)) = case x of NONE => NONE | SOME sth => f sth;
fun ((x:'a option, y:'b option ) ??> (f:'a -> 'b -> 'c option)) =
  case (x, y) of (SOME x, SOME y) => f x y | _ => NONE
(* (x +> f) lifts a normal function to the option level.*)
fun (x +> f) = Option.map f x;
\<close>

ML\<open> fun is_some_true (bopt:bool option) = case bopt of NONE => false | SOME b => b; \<close>

text\<open> AutoCorres related opearations.\<close>

(* Returns the list of structs generated by the C parser *)
ML\<open> fun get_struct_name_from_c_parser c_file thy ctxt =
 CalculateState.get_csenv thy c_file
 |> the
 |> ProgramAnalysis.get_senv
 |> map fst
 |> map (Proof_Context.read_typ ctxt)
\<close>

ML\<open> fun get_struct_info thy file_name =
 Symtab.lookup (HeapInfo.get thy) file_name
|> Utils.the' "get_struct_info failed."
|> #heap_info
|> #structs
\<close>

ML\<open> fun get_field_info (struct_info:HeapLiftBase.struct_info Symtab.table) ty_name =
 Symtab.lookup struct_info (ty_name ^ "_C")
|> Utils.the' "get_field_info failed."
|> #field_info ;
\<close>

ML\<open> fun get_field_names (field_info:HeapLiftBase.field_info list) =
 field_info |> (map (cut_C o Long_Name.base_name o get_name o #getter));
\<close>

ML\<open> fun get_getters (field_info:HeapLiftBase.field_info list) = field_info |> map #getter;\<close>

ML\<open> fun ac_mk_heap_getters_for file_nm thy (st_C_nm : string) =
(* checks if autocorres generates heap_getters for a given uval. Returns a boolean value.*)
 let
  val opt_hinfo                    = Option.map #heap_info (Symtab.lookup (HeapInfo.get thy) file_nm);
  fun get_struct_info heap_info    = Symtab.lookup (#structs heap_info) st_C_nm;
  val opt_sinfo                    = opt_hinfo ?> get_struct_info;
  fun get_heap_getters hinfo sinfo = Typtab.lookup (#heap_getters hinfo) (#struct_type sinfo);
  val opt_heap_getters             = (opt_hinfo, opt_sinfo) ??> get_heap_getters
  val flag                         = is_some opt_heap_getters;
 in flag end;
\<close>

(* Currently, this function get_c_file_name_from_path is not used.*)
ML\<open> fun get_c_file_name_from_path path =
 String.tokens (fn splitter => splitter = #"/") path |> List.last;
 (* Test *)
 get_c_file_name_from_path "~/l4.verified/autocorres/AutoCorres"
\<close>

(* Japheth recommended to use mk_term developed by David.G. *)
ML\<open> val example_of_dynamic_antiquotation =
 @{mk_term "a ?b \<Longrightarrow> ?c" (b, c )} (@{term "id"}, @{term "Suc 0"});
(*
(* The mk_term anti-quotation does not check the types.*)
Syntax.check_term @{context} example_of_dynamic_antiquotation;
*)
\<close>

text\<open> tacticals \<close>

ML\<open> fun SOLVE_ONE (tac:tactic) (thm:thm) =
(* SOLVE_ONE is a specialization of SOLVE. *)
let
 val result = tac thm |> Seq.pull;
 fun solved_one new_thm = ((Thm.nprems_of thm) = (Thm.nprems_of new_thm + 1));
in
 case result of
   NONE => Seq.empty (* tac thm failed *)
 | SOME (thm_changed, _) => (if solved_one thm_changed
    then Seq.cons thm_changed Seq.empty
    else Seq.empty (* tac did not discharge a subgoal. *))
end;
\<close>

(*
fun DETERM_TIMEOUT delay tac st =
  Seq.of_list (the_list (Timeout.apply delay (fn () => SINGLE tac st) ()))
*)

ML\<open> (* TIMEOUT and TIMEOUT_in *)
local
 (* DETERM_TIMEOUT was written by Jasmin Blanchette in nitpick_util.ML.
  * This version has exception handling on top of his version.*)
 fun DETERM_TIMEOUT delay tac st =
   Seq.of_list (the_list (Timeout.apply delay (fn () => SINGLE tac st) ()
    handle Timeout.TIMEOUT _ => NONE));
in
 (* (TIMEOUT tac) returns a tactic that fail, if tac cannot return in 3.14 seconds.*)
 (* TODO: This is a quick hack! Double-check the code.*)
 (* I am not sure if I implemented exception handling correctly.*)
 fun TIMEOUT_in real tac = DETERM_TIMEOUT (seconds real) tac;
 fun TIMEOUT tac         = DETERM_TIMEOUT (seconds 3.14) tac;
end\<close>

ML\<open> (* Taken from Cookbook. *)
structure Result = Proof_Data
  (type T = unit -> term
   fun init _ () = error "Result")

val result_cookie = (Result.get, Result.put, "Result.put");

let
   fun after_qed thm_name thms lthy =
        Local_Theory.note (thm_name, (flat thms)) lthy |> snd
   fun setup_proof (thm_name, src) lthy =
     let
       val trm = Code_Runtime.value lthy result_cookie ("", Input.text_of src)
     in
       Proof.theorem NONE (after_qed thm_name) [[(trm, [])]] lthy
     end
   val parser = Parse_Spec.opt_thm_name ":" -- Parse.ML_source
in
   Outer_Syntax.local_theory_to_proof @{command_keyword "foobar_prove"}
     "proving a proposition"
       (parser >> setup_proof)
end;
\<close>

text\<open> Lemma buckets written by Dan.\<close>

ML \<open> signature NAMED_THMS_EXT =
sig
  include NAMED_THMS
  val add_local : thm -> local_theory -> local_theory
  val del_local : thm -> local_theory -> local_theory
end

functor Named_Thms_Ext(val name: binding val description: string): NAMED_THMS_EXT =
struct
  structure Named_Thms = Named_Thms(val name = name val description = description)
  open Named_Thms

  fun add_local thm = Local_Theory.notes [((Binding.empty,[Attrib.internal (K add)]),[([thm],[])])] #> snd
  fun del_local thm = Local_Theory.notes [((Binding.empty,[Attrib.internal (K del)]),[([thm],[])])] #> snd

end
\<close>

text\<open> Instantiation of type class.\<close>

ML\<open> fun local_setup_instantion arities lthy=
 Class.instantiation_cmd arities (Local_Theory.exit_global lthy);\<close>

ML\<open> fun local_setup_instance lthy =
 Class.prove_instantiation_instance (fn ctxt => Class.intro_classes_tac ctxt []) lthy;\<close>

ML\<open> fun local_setup_instantiation_definition_instance arities local_setup_definition lthy = lthy |>
 local_setup_instantion arities |>
 local_setup_definition |>
 local_setup_instance;\<close>

ML \<open>
fun test_read_term lthy (s : string) : bool =
 (  Proof_Context.read_term_pattern lthy s ; true)
handle ERROR _ => false

fun is_cogent_C_val lthy (typ : string) : bool =
  test_read_term lthy ("type_rel _ TYPE(" ^ typ ^ ")")

fun is_cogent_C_heap lthy (typ : string) : bool =
  test_read_term lthy ("is_valid _ (_ :: " ^ typ ^ " ptr)")
\<close>

ML \<open> 
fun local_setup_instantiation_definition_instance_if_needed 
   C_typ class
   already_defined local_setup_definition 
   lthy = 
  if already_defined lthy C_typ then
      (tracing (C_typ ^ " is already a " ^ class);
           lthy )
  else 
    local_setup_instantiation_definition_instance 
    ([C_typ],[],class)  local_setup_definition lthy
\<close>
(* TODO: merge it with the previous function *)
ML \<open> 
fun local_setup_instantiation_definition_instance_for_types 
   C_typ class
   for_types local_setup_definition 
   lthy = 
  if C_typ  is_in for_types then
       local_setup_instantiation_definition_instance 
    ([C_typ],[],class)  local_setup_definition lthy
  else 
     lthy\<close>



text\<open> Auxiliary functions for writing tactic.\<close>

ML\<open> fun scrape_C_types_term t = let
    fun filter_Const P (Const (c_name, _)) = if P c_name then [c_name] else []
      | filter_Const P (f $ x) = filter_Const P f @ filter_Const P x
      | filter_Const P (Abs (_, _, t)) = filter_Const P t
      | filter_Const _ _ = []
    fun c_type_name str = String.tokens (fn x => x = #".") str
                          |> filter (String.isSuffix "_C") |> take 1
  in t
     |> filter_Const (c_type_name #> null #> not)
     |> map c_type_name |> List.concat
     |> distinct (op =)
  end;
\<close>

ML\<open> val scrape_C_types = scrape_C_types_term o Thm.concl_of; \<close>

ML\<open> fun make_thm_index guess thms =
 let
  val nmths = map swap (maps (fn t => map (pair t) (guess t)) thms)
 in Symtab.make_list nmths end;
\<close>

ML\<open> fun lookup_thm_index table = maps (Symtab.lookup_list table) #> distinct Thm.eq_thm \<close>


ML \<open>
(* Inverse of space_implode *)
fun split_on (sep: string) (s: string) =
      if sep = "" then error "split_on: empty separator" else let
        val k = String.size sep
        val n = String.size s
        fun split i l =
            if i+l+k > n
              then if i <= n then [String.extract (s, i, NONE)] else []
              else if String.substring (s, i+l, k) = sep
                   then String.substring (s, i, l) :: split (i+l+k) 0
                   else split i (l+1)
        in split 0 0 end;

assert (split_on ".." "..a..b..c.....d" = ["", "a", "b", "c", "", ".d"]) "test split_on"
\<close>


end
