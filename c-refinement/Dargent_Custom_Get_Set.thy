(*

This file deals with custom getters and setters in case of custom layouts.
It also register uvals read from the table file in the theory.

The three main functions are
1) generate_isa_getset_records_for_file: generates a direct and non monadic definition of custom
getters and setters by inspecting the C (monadic) definition

2) local_setup_getset_lemmas which generates the get/set lemmas and prove them (similarly
to local_setup_take_put_member_case_esac_specialised_lemmas)

To show the get/set lemmas that ought to be proven, use the following snippset:
ML \<open> val lems = mk_getset_lems "variant_dargentisa.c" @{context} \<close>
ML \<open>lems  |> map (string_of_getset_lem @{context})|> map tracing\<close>

These get/set lemmas should be proven before the Take, Put, .. lemmas.

3) local_setup_getset_sanity_lemmas which generates sanity checks for
custom getters and setters (that they are only concerned with the bits 
specified by the layouts). These lemmas are not necessary for the refinement
proof.

This function is outdated in the sense that it was implemented before 4), which is more convincing.

4) local_setup_getter_correctness which generates correctness theorems for getters (that
they manipulate data according to the layouts). See the last part of this file.
Use the following snipset:
context Example begin
local_setup \<open> local_setup_getter_correctness "example.c"\<close>

thm GetSetSanity
end

*)
theory Dargent_Custom_Get_Set
imports AutoCorres.AutoCorres
  Tidy
  Specialised_Lemma_Utils
  Read_Table
  Value_Relation
begin

ML \<open>fun get_uval_custom_layout_records_no_redundancy uvals =
(uvals |> get_uval_custom_layout_records 
    |> List.map (fn x => (get_ty_nm_C x, get_uval_custom_layout x)) |> rm_redundancy)
\<close>

(* These lemmas help simplifying the monadic custom C getters and setters, that are inspected
to devise a corresponding direct (non monadic) definition.
 *)

lemma gets_comp : "do x <- gets f ;
                     gets (f' x) od
                     =
                  gets (\<lambda> s . f' (f s) s)"
  by monad_eq
(*
lemma gets_return : "do x <- gets f ;
                     return (g x) od = gets (g o f)"
  by monad_eq
*)

lemma modify_comp: "do _ <- modify f ; modify f' od = modify (f' o f )"
  by (monad_eq)

lemma ptr_set_comp :
   "(\<lambda>x. x(ptr := f (x ptr))) o (\<lambda>x. x(ptr := f' (x ptr))) = (\<lambda>x. x(ptr := f (f' (x ptr))))"
(*  proof obtained by sledgehammer *)
proof -
have "\<forall>fa. ((\<lambda>fa. fa(ptr := f (fa ptr))) \<circ> (\<lambda>f. f(ptr := f' (f ptr)))) fa = fa(ptr := f (f' (fa ptr)))"
  by (simp add: fun_upd_same)
  then show ?thesis
    by blast
qed

(* Lemmas for variants (that involves conditions) *)
lemma condition_cst : " condition (\<lambda> _. b) u v = (if b then u else v)"
  by simp
  
lemma modify_if : "(if b then modify f else modify g) = 
  modify (\<lambda> x. if b then f x else g x)"
  by simp

lemma ptr_set_if :
   "(if b then x(ptr := t) else x(ptr := u)) = 
    x(ptr := if b then t else u)"
  by simp

ML \<open>
(* The callgraph is used to unfold any auxiliary function in the monadic definition of 
C getter/setter
*)
type callgraph = Symtab.key Binaryset.set Symtab.table;
(* TODO: use get_fun_info instead of c-parser callgraph *)
fun get_callgraph thy Cfile : callgraph =
 CalculateState.get_csenv thy Cfile
  |> Utils.the' ("get_callgraph: C file " ^ Cfile ^ " not loaded") 
|> ProgramAnalysis.compute_callgraphs |> #callgraph


(* returns the list of called functions in the body of
 fn_name *)
(* could also used FunctionInfo.callees in AutoCorres instead
of the callgraph *)
fun called_funs (g : callgraph) (fn_name : string) =
    case Symtab.lookup g fn_name of
   SOME t => Binaryset.listItems t
   | NONE => []

(* returns the list of called functions in the body of
 fn_name and recursively, the list of called functions
in the body of the called functions *)
fun rec_called_funs g (fn_name : string) =
  let
    val l =  called_funs g fn_name
  in
  l @ (List.map (rec_called_funs g) l
  |> List.concat)
end

\<close>





ML \<open>

(* thm[of t1 t2] ~ thm_of ctxt [t1, t2] thm *)
fun thm_of ctxt vars = 
  Rule_Insts.of_rule ctxt (List.map SOME vars, []) []

(* thm[simplified thms] ~ thm_simp ctxt thms thm 
(not exactly equivalent as the first version clears the
simplication set)
*)
fun thm_simp ctxt thms = 
Simplifier.asm_simplify (ctxt addsimps thms)

(* thm1[THEN thm2] ~ thm_THEN ctxt thm2 thm1 *)
fun thm_THEN thm2 thm1 =
thm1 RSN (1 , thm2) ;

(* thm1[OF thms] ~ thm_OF thm1 thms *)
fun thm_OF thm1 thms =
thm1 OF thms ;
\<close>

(* The purpose of this lemma is to unify a goal. More precisely, we provide P and Q and let isabelle
infer f *)
lemma unify_goal_auxiliary : "\<And> P Q f. P f \<Longrightarrow> Q f \<Longrightarrow> Q f"
  by simp

ML \<open>
(* 
replace a goal A \<Rightarrow> P f with
A \<Rightarrow> Q f \<Rightarrow> Q f, for sP the string defining P
(typically a lambda), and sQ the string defining Q
*)
fun unify_change_goal ctxt sP sQ (* simps *) thm =
  thm |> thm_THEN
(
@{thm unify_goal_auxiliary}
|> thm_of ctxt [sP, "_", sQ]
|> Simplifier.asm_full_simplify ctxt)

(* 
replace a goal A \<Rightarrow> P f with
A \<Rightarrow> undefined = Q f \<Rightarrow> undefined = Q f,
 for sP the string defining P
(typically a lambda), and sQ the string defining Q
*)
fun unify_change_goal_eq ctxt sP sQ  =
  unify_change_goal ctxt sP 
    ("\<lambda> f.  undefined = " ^ sQ ^ " f") 
\<close>

(* Complementary easy lemmas about heap setters (proved by fastforce):
- heap_t1_C_update f o heap_t1_C_update f' = heap_t1_C_update (f o f')
- (if b then heap_t1_C_update f z else heap_t1_C_update g z) = 
  heap_t1_C_update (\<lambda> x. if b then f x else g x) z

They are used to simplify the monadic definition of custom getters and setters
when devising a direct definition of them.
*)

ML \<open>

fun make_heap_setter_thm name statement vars ctxt =
let
 val term = @{term Trueprop} $ Proof_Context.read_term_pattern ctxt statement
 val thm = Goal.prove ctxt vars [] term 
    (fn { context = ctxt, prems = _} => fast_force_tac ctxt 1 )
 val (_, ctxt) = Local_Theory.note ((Binding.name name, []), [thm]) ctxt 
in
 (thm, ctxt)
end

fun make_heap_setter_comp_thm heap_setter ctxt =
let
 val name = List.last (String.tokens (fn #"." => true | _ => false) heap_setter)  
   ^ "_comp"
 val statement = heap_setter ^ " f o " ^ heap_setter ^ " f' = "
              ^ heap_setter ^ " (f o f')"
 val vars = ["f", "f'"] 
in
   make_heap_setter_thm name statement vars ctxt
end

fun make_heap_setter_if_thm heap_setter ctxt =
let
 val name = List.last (String.tokens (fn #"." => true | _ => false) heap_setter)  
   ^ "_if"

 val statement = 
  "(if b then " ^ heap_setter ^ " f z else "
                ^ heap_setter ^ " f' z) = "
  ^ heap_setter ^ " (\<lambda> x. if b then f x else f' x) z"
 val vars = ["b", "z", "f", "f'"] 
in
   make_heap_setter_thm name statement vars ctxt
end
\<close>

ML \<open>
(* generate the isabelle getter term, depending on an argument named w,
 by inspecting the C getter definition as given by get_def_thm (which should
be totally unfolded)
heap_getter: the name of the heap getter, e.g. heap_t1_C
*)
fun generate_getter_term ctxt getter_name heap_getter get_def_thm =
get_def_thm
|>
Rule_Insts.of_rule ctxt ([SOME "ptr"], []) [] |>
thm_simp
(* rewrites return into gets 
(happened to be useful for variant constructors without argument)
*)
(Raw_Simplifier.flip_simp @{thm NonDetMonadLemmas.gets_to_return }ctxt)

([
(* We add this rewrite rule to remove the guards *)
  (Proof_Context.read_term_pattern ctxt 
   "\<And> (e :: lifted_globals \<Rightarrow> _). guard e = gets (\<lambda>_  . ())"
  |> Thm.cterm_of ctxt  |> Thm.assume)
  ] 
  @ @{thms (* gets_return *) gets_comp NonDetMonadEx.condition_gets }  )
|> thm_simp 
(* rewrite in the then and else statements *)
(Simplifier.add_cong @{thm if_cong} ctxt)
 @{thms comp_def }
(* Here we should have a conclusion of the shape
getter ptr = gets (\<lambda>s . f s)
*)
|> unify_change_goal_eq ctxt 
("(\<lambda> f. " ^ getter_name ^ "' ptr = gets (\<lambda>s . f  (" ^ heap_getter ^ " s ptr)))")
"(\<lambda> f. f w)" 
|> Thm.concl_of 
|> Utils.rhs_of_eq
\<close>

ML \<open>
(* generate the isabelle setter term, depending on arguments named w and v (the new value),
 by inspecting the C setter definition as given by set_def_thm (which should
be totally unfolded)

A simplification rule of the shape
 " heap_t1_C_update f o heap_t1_C_update f' = heap_t1_C_update (f o f')"
should be first added to the context.

heap_setter: the name of the heap setter, e.g. heap_t1_C_update
*)
fun generate_setter_term ctxt setter_name heap_setter heap_setter_thms setter_thm =
setter_thm
|> 
Rule_Insts.of_rule ctxt ([SOME "ptr", SOME "v"], []) [] |>
thm_simp ctxt
([
(* We add this rewrite rule to remove the guards *)
  (Proof_Context.read_term_pattern ctxt 
   "\<And> (e :: lifted_globals \<Rightarrow> _). guard e = gets (\<lambda>_  . ())"
  |> Thm.cterm_of ctxt  |> Thm.assume)
  ] 
  (* @ @{thms modify_comp ptr_set_comp} *)
 
 )

(* This tackles conditions (if variants) *) 
|> thm_simp
 (* rewrite in the then and else statements *)
 (Simplifier.add_cong @{thm if_cong} ctxt)
 (@{thms modify_comp ptr_set_comp comp_def condition_cst modify_if ptr_set_if} @ heap_setter_thms)
(* at this point, it should be of shape 
set_field ptr v \<equiv> modify (heap_update (\<lambda>x. x(ptr :=
  f (x ptr))

f may be a complicated 'if' statement
*)
(* for debugging purpose *)
(* |> unify_change_goal_eq ctxt "(\<lambda> f. I)" "this displays the current term" *)
|> thm_THEN @{thm  HOL.meta_eq_to_obj_eq}
|> unify_change_goal_eq ctxt 
("(\<lambda> f. " ^ setter_name ^ 
"' ptr v = modify (" ^ heap_setter ^ " (\<lambda>x . x(ptr := f  (x ptr)))))")
"(\<lambda> f. f w)" 

|> Thm.concl_of 
|> Utils.rhs_of_eq
\<close>


ML \<open>
(* define an Isabelle function with a provided term depending on a
list of named variables. *)
fun define_function name vars term ctxt = 
 case Utils.define_const_args name false term
(List.map (fn x => (x , Term.dummyT)) vars) ctxt of
   (_, thm, ctxt) => GetSetDefs.add_local thm ctxt 
 \<close>

ML \<open>



(* returns a definition theorem for a C function named fn_named, where
all the recursively called functions in the body have been unfolded using
theorems provided by get_thm_def
 *)
fun unfold_thm (g : callgraph) (fn_name : string) 
   (get_thm_def : string -> Proof.context -> thm)  ctxt =
   let  
    val called_funs = rec_called_funs g fn_name
    (* For debugging purpose *)
    (*
    val _ = writeln ("unfolding " ^ fn_name) 
    val _ = writeln (String.concatWith ", " called_funs)
    val _ = writeln 
        ( "apply(simp only: " ^
             (String.concatWith " "  
                      (called_funs |> map (fn s => s ^ "'_def")))
         ^ ")") *)

    (* generate nice definitions of C getters *)
    val called_funs_def =  List.map (fn s => get_thm_def s ctxt) called_funs
in
   get_thm_def fn_name ctxt |> thm_simp ctxt called_funs_def
end

\<close>


ML \<open>

(* 
add to the context the definition of an isabelle getter/setter (depending
on the provided arguments get_thm_def, generator, and args) corresponding the
C getter/setter named fn_name.
also, adds a simplified definition theorem of the C getter/setter.
*)
fun generate_isa_get_or_set g fn_name args get_thm_def generator ctxt =
let   
    val isa_fn_name = "deref_" ^ fn_name
    val simplified_thm_name = fn_name ^ "'_def'"
    val _ = tracing ("generate_isa_get_or_set: generating " ^ isa_fn_name ^ " and " ^ simplified_thm_name)
    (* The unfolded definition of the monadic getter/setter *)
    val fn_def_thm = unfold_thm g fn_name 
      (fn s => ((* tracing s ; *) get_thm_def s) ) ctxt
    val term = generator fn_def_thm
    val (thm_def, ctxt) = Utils.define_lemma simplified_thm_name fn_def_thm ctxt
    val ctxt = GetSetDefs.add_local thm_def ctxt
in
 (isa_fn_name, define_function isa_fn_name args term ctxt : Proof.context)
end

(* heap_fn : the name of the heap getter, e.g. heap_t1_C *)
fun generate_isa_get g heap_fn fn_name ctxt =
generate_isa_get_or_set g fn_name ["w"] tidy_C_fun_def
  (generate_getter_term ctxt fn_name heap_fn) ctxt

(* given the name of a C function, returns the definition theorem and 
slightly simplifies it *)
fun fn_C_def_thm fn_C_name ctxt =
  Proof_Context.get_thm ctxt (fn_C_name ^ "'_def")
 |> thm_simp ctxt @{thms unknown_bind_ignore }  
  (* this additionnal simplification is useful when unfolding
   endianness auxiliary functions, such as le_u16_swap
  *)

(* heap_fn : the name of the heap setter, e.g. heap_t1_C_update *)
fun generate_isa_set g heap_fn fn_name heap_setter_thms ctxt =
generate_isa_get_or_set g fn_name ["w", "v"]  fn_C_def_thm (* tidy_C_fun_def does not work for setters *)
  (generate_setter_term ctxt fn_name heap_fn heap_setter_thms) ctxt

fun generate_isa_getset g heap_getter heap_setter heap_setter_thms (* ty *)
   (l : table_field_layout) 
   ctxt = 
 let
   val (isa_getter_name, ctxt) = generate_isa_get g heap_getter (# getter l) ctxt
   val (isa_setter_name, ctxt) = generate_isa_set g heap_setter (# setter l) heap_setter_thms ctxt
 in
   (((# getter l , isa_getter_name), (#setter l, isa_setter_name)), ctxt)
 end



(* generate the isabelle setter/getters and simplified definitions of the C getter/setter
for a given record type ty with specified C getter/setters in l
*)
fun generate_isa_getset_record g (heap_info : HeapLiftBase.heap_info) (ty, l) ctxt =
  let
    val _ = tracing ("generate_isa_getset_record: generating getter/setter for " ^ ty)
    val heap_getter = ( Typtab.lookup (#heap_getters heap_info) 
        (Syntax.read_typ ctxt ty)) |> 
           Utils.the' ("heap getter not found for " ^ ty) |> 
            fst
    val heap_setter = ( Typtab.lookup (#heap_setters heap_info) 
        (Syntax.read_typ ctxt ty)) |> the |> fst
    val (heap_setter_comp, ctxt) = make_heap_setter_comp_thm heap_setter ctxt
    val (heap_setter_if, ctxt) = make_heap_setter_if_thm heap_setter ctxt
    val heap_setter_thms = [heap_setter_comp, heap_setter_if]
    val (lays, ctxt) =   fold_map 
   (generate_isa_getset g heap_getter heap_setter heap_setter_thms)
     l ctxt
  in
    (lays, ctxt)
 end

(* generate isabelle setter/getters and simplified definition of C getter/setters
induced by a list of uvals (typically read from a table file).
*)
fun generate_isa_getset_records g heap_info uvals ctxt =
  let
    (* the hard job is done here *)
    val (getsetl, ctxt) = 
     fold_map (generate_isa_getset_record g heap_info)
     (uvals |> get_uval_custom_layout_records_no_redundancy)
   
    ctxt
    val getsetMap = getsetl |> List.concat |>
       ListPair.unzip |> List.revAppend |>
      Symtab.make
      |> Symtab.map (fn _ => Syntax.read_term ctxt)
    val _ = tracing (@{make_string} getsetMap)
    fun make_uval (uval : table_field_layout uval) : field_layout uval =
       uval_map 
        (fn info => make_field_layout info 
      {
        isa_getter = (Symtab.lookup getsetMap (# getter info) |> Utils.the' "getter not found"),
        isa_setter = (Symtab.lookup getsetMap (# setter info) |> Utils.the' "setter not found")
     }
  )
       uval
    val uvals = List.map make_uval uvals
  in
    (uvals, ctxt)
  end



 \<close>

(* 
This ML function generate custom getters/setters in Isabelle from
the C custom getters/setters.

More precisely, the involved steps are:
1. get the names of custom C getters/setters from the table file
2. prove a simplified definition of them by unfolding the auxiliary 
   called C functions and using Tidy lemmas (thus produces Cgetter_def' 
   lemmas in the context). 
3. infer an isabelle definition of custom getter/setters by inspecting
   these simplified definition (and performing further simplification, such
   as removing all guards)
4. Put a uvals in a Theory Data so we don't need to read the table file again later.

The simplified definitions are thought to be used later when proving that
the C and isabelle custom getters/setters match.

 *)
ML \<open>
(* The additionnal parameter locale could certainly be removed *)
fun generate_isa_getset_records_for_file filename locale thy =
  let
    val uvals = read_table filename thy
    val g = get_callgraph thy filename : callgraph
    val heap_info = (Symtab.lookup (HeapInfo.get thy) 
     filename |> the  |> #heap_info)
    val ctxt = Named_Target.init locale thy
    val (uvals, ctxt) = generate_isa_getset_records g heap_info uvals ctxt
    val thy = Named_Target.exit ctxt
  in
    UVals.map (Symtab.update (filename, uvals)) thy
  end
 \<close> 

(*


Now, the generation of getset lemmas


*)               

ML \<open>
(* 1. `get o set = id`
2. `get_a o set_b = get_a`
3. `C_get = isabelle_get`
4. `C_set = isabelle_set`

more exactly, the first one is rather

1. `val_rel x new_val \<Longrightarrow> val_rel x (get (set t new_val))`

because get o set = id is too strict, as it does not hold for variants: if a field is a variant,
then the associated getter erases the irrelevant fields. Thus equality is too strong,
but we can replace them with value relation preservation
 *)
datatype getSetLemType = 
  GetSet | GetASetB | GetDef | SetDef

(* adapted from the lem type *)
type getset_lem = { prop : term, typ : getSetLemType, name : string, mk_tactic: Proof.context -> tactic} 


val cheat_tactic : Proof.context -> tactic = fn context => Skip_Proof.cheat_tac context 1

(* for debugging purpose *)
fun string_of_getset_lem ctxt (lem : getset_lem) =
  "lemma " ^ # name lem ^ "[GetSetSimp] : \"" ^
   Syntax.string_of_term ctxt (# prop lem) ^ "\""
  ^ "\n  sorry"

\<close>


(* Section about simplifying chains of Array updates (for the deterministic vs indeterministic
getter/setter correspondence). 

Sometimes you need to compare chains of Array updates at different indices, of the same array.

The definitions and lemmas below are used by the tactic array_updates_simp to transform such a chain
into a canonical, where the updates are sorted by their indices and duplicates are removed (only
the last update at a specific index is relevant).
 *)

fun array_updates where
  "array_updates arr [] = arr"
| "array_updates arr ((n, v) # tail) = array_updates (Arrays.update arr n v) tail"

lemma array_update_updates : "Arrays.update arr n v = array_updates arr [(n,v)]"
  by simp

lemma array_updates_append :
   "\<And> arr. array_updates (array_updates arr l1) l2 = array_updates arr (l1 @ l2)"
  by(induct l1;clarsimp)
   
lemma array_updates_insert :  "\<And> arr. array_updates (Arrays.update arr aa ba) l =
       array_updates arr (insort_key fst (aa, ba) l)"
by(induct l;clarsimp)


lemma array_updates_order :
    " \<And> arr. array_updates arr l \<equiv> array_updates arr (sort_key fst l)"
  apply(induct l; clarsimp)
  apply(simp add:array_updates_insert)
  done

fun remdups_key_adj :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a list \<Rightarrow> 'a list" where
 "remdups_key_adj f [] = []" |
"remdups_key_adj f [x] = [x]" |
"remdups_key_adj f (x # y # xs) = (if f x = f y then remdups_key_adj f (y # xs) else x # remdups_key_adj f (y # xs))"

 
lemma array_updates_remdups_adj_aux :
   
 "(\<forall> arr. f = fst \<longrightarrow>  array_updates arr l = array_updates arr (remdups_key_adj f l)) "  
  
  by(rule remdups_key_adj.induct[of _ f l]; clarsimp)
  


lemma array_updates_remdups_adj :
  "  array_updates arr l \<equiv> array_updates arr (remdups_key_adj fst l)"
  apply(simp add: HOL.atomize_eq)
  apply(rule allE[ OF  array_updates_remdups_adj_aux])
  apply (erule impE;simp)
  done

(* this intermediate definition prevents simplification to loop
when using array_updates_simp
*)
definition simplified_array_updates
  where "simplified_array_updates = array_updates"

lemma array_updates_simp :
  "array_updates arr l \<equiv> simplified_array_updates arr (remdups_key_adj fst (sort_key fst l))"
  apply (subst  array_updates_order)
  apply (subst array_updates_remdups_adj)
  apply (simp add:simplified_array_updates_def)
  done

(* 

rewrite Arrays.update (Arrays.update (Arrays.update 7 a) 7 b)) 3 c) as 
Arrays.update (Arrays.update 3 c) 7 b
(i.e., remove duplicates, and sort the indices)
*)
ML \<open>
fun array_updates_simp ctxt : int -> tactic = 
simp_tac (clear_simpset ctxt addsimps @{thms array_update_updates array_updates_append})
THEN_ALL_NEW
simp_tac (clear_simpset ctxt addsimps @{thms array_updates_simp})
THEN_ALL_NEW
simp_tac (ctxt addsimps @{thms simplified_array_updates_def})
\<close>




(* This lemmas is used to prove some
get/set lemmas (more exactly, to prove the correspondence between
the monadic and the direct definitions of custom getter/setters).
It is added to the set of simplification lemmas.

 *)
lemma unat_le : " 2 ^ LENGTH('a :: len) \<le> n \<Longrightarrow> unat (x :: 'a word) < n"
  by (meson le_def le_trans unat_lt2p)


ML\<open> 
(* 
proves a statement of the shape (for getters)

`
monadic_getter ptr = do _ <- guard (\<lambda>s. is_valid_t2_C s ptr);
                  gets (\<lambda>s. direct_getter (heap_t2_C s ptr))
                od"
`

or (for setters)

`
monadic_setter ptr v =
 do _ <- guard (\<lambda>s. is_valid_t2_C s ptr);
  modify (heap_t2_C_update (\<lambda>a. a(ptr := direct_setter (a ptr) v)))
 od
`

The tactic does the following:

(* this unfolds the definitions of the monadic and the direct getter/setter *)
apply (simp add: GetSetDefs)
(* This line was worked out by looking at some examples.
   It may be incomplete *)
apply(simp add:L2opt unat_le condition_cst condition_cst)
by (monad_eq simp add:comp_def)

*)
fun custom_get_set_monadic_direct_tac ctxt = let
    val gets = Proof_Context.get_thms ctxt
    val get  = Proof_Context.get_thm ctxt    
    val getset_defs = GetSetDefs.get ctxt; 
    val facts = @{thms L2opt unat_le condition_cst}
in  

  simp_tac (ctxt addsimps getset_defs) THEN_ALL_NEW
  simp_tac (ctxt addsimps facts) THEN_ALL_NEW
  (fn _ => monad_eq_tac (ctxt addsimps @{thms comp_def ucast_id})) 
  THEN_ALL_NEW
   array_updates_simp ctxt

  (* fn _ => cheat_tactic ctxt  *)
end


(* 
proves a statement of the shape 

`
get_a (set_b f v) = get_a f
`


*)


fun custom_get_set_different_field_tac ctxt = 
let
    val gets = Proof_Context.get_thms ctxt
    val get  = Proof_Context.get_thm ctxt    
    val getset_defs = GetSetDefs.get ctxt;
    val tag_defs =
      gets "tag_t_defs" handle ERROR _ => []
in  
  asm_full_simp_tac (ctxt addsimps getset_defs addsimps tag_defs) 
 THEN_ALL_NEW
   K (TRY ( REPEAT_SOME
  (K (Method.intros_tac ctxt @{thms conjI impI} []))))
  THEN_ALL_NEW
 bw_tac_signed ctxt
THEN_ALL_NEW asm_full_simp_tac ctxt

  (* fn _ => cheat_tactic ctxt  *)

end
\<close>

(* This rewrite x \<noteq> 0 with x && 0 after
unfolding the definition of the value relation
for booleans
*)
(*
lemma bool_val_rel_simp :
  " ((x = 0) \<or> (x = 1)) \<Longrightarrow>
 ((x \<noteq> 0) = ( (x :: 8 word) && 1 = 1))"
  by (erule disjE; simp)    
*)

(* This avoids disjonctive elimination when 
dealing with booleans *)
lemma word8_le1 : "((x :: 8 word) = 0 \<or> x = 1) \<equiv> x \<le> 1"
  by unat_arith

ML \<open>
(*

proves a statement of the shape
"val_rel x v \<Longrightarrow>  val_rel x (get (set b v))"
*)
fun custom_get_set_same_field_tac ctxt = 
let

   val valsimps = ValRelSimp.get ctxt;
   val getset_defs = GetSetDefs.get ctxt;
   val gets = Proof_Context.get_thms ctxt ;
   val tag_defs =
      gets "tag_t_defs" handle ERROR _ => []
   val variable = Syntax.read_term ctxt "v";
in  
(* Sometimes, for example when v is a pointer,
 it helps to deconstruct it *)
Induct.cases_tac ctxt false [ [ SOME variable ] ] NONE []
THEN_ALL_NEW
(* substitute *)
hyp_subst_tac ctxt
THEN_ALL_NEW
asm_full_simp_tac (ctxt addsimps valsimps
addsimps @{thms word8_le1}
)
THEN_ALL_NEW 
(*
With nested variants, the disjunction elimination 
may create a very large number of goals  
(exponentially in some respect, I guess), because all the 
possibilites are then investigated.
This needs to be fixed.
*)
K (TRY ( Method.elim ctxt  @{thms exE conjE disjE } []
 |> Method.NO_CONTEXT_TACTIC ctxt))
(* THEN_ALL_NEW
(* not necessary, but increases the speed *)
clarsimp_tac ctxt *)
THEN_ALL_NEW
(* the following was copied from custom_get_set_different_field_tac
Calling custom_get_set_different_field_tac does not work here,
because the THEN_ALL_NEW is not associative. This causes
a problem because the bw_tac_signed tactic acts on all goals,
even after THEN_ALL_NEW (not only the new goals emerging
from the previous one), some of them
may not be simplified enough at this time.
 *)
  asm_full_simp_tac (ctxt addsimps getset_defs addsimps tag_defs) 
 THEN_ALL_NEW
   K (TRY ( REPEAT_SOME
  (K (Method.intros_tac ctxt @{thms conjI impI} []))))
  THEN_ALL_NEW
  (bw_tac_signed ctxt )
THEN_ALL_NEW asm_full_simp_tac ctxt
end

\<close>







ML \<open>
fun make_getset_prop_gen prms cncl ctxt : term =
  let
   val clean = HOLogic.mk_Trueprop o strip_atype
   val term = mk_meta_imps 
      (map clean prms) 
      (clean cncl) ctxt |> Syntax.check_term ctxt;
  in
     term
  end
\<close>



ML \<open>
fun mk_getset_prop (info : field_layout) ctxt : term =  
  let
   val prms = [ 
   @{term "val_rel x v"} 
]
   val cncl = @{term "\<lambda> getter setter. val_rel x (getter (setter b v))"}
         $ (# isa_getter info) $ (# isa_setter info)   
  in
     make_getset_prop_gen prms cncl ctxt
  end
\<close>

ML \<open>
fun mk_getdef_prop heap_getter is_valid_struct     
  (info : field_layout) ctxt : term =  
  let
   
   
   val field_getter    = #getter info ^ "'" |> Syntax.read_term ctxt;


   val cncl =
       @{term "\<lambda> isa_getter C_getter is_valid heap_getter. 
   C_getter ptr = do _ <- guard (\<lambda>s. is_valid s ptr);
                gets (\<lambda>s. isa_getter (heap_getter s ptr)) 
                od"}
         $ (# isa_getter info) $ field_getter $ is_valid_struct 
       $ heap_getter   
  in
     make_getset_prop_gen [] cncl ctxt
  end
\<close>

ML \<open>
fun mk_setdef_prop heap_setter is_valid_struct     
  (info : field_layout) ctxt : term =  
  let
   
   
   val field_setter    = #setter info ^ "'" |> Syntax.read_term ctxt;


   val cncl =
       @{term "\<lambda> isa_setter C_setter is_valid heap_setter. 
   C_setter ptr v = do _ <- guard (\<lambda>s. is_valid s ptr);
   modify (heap_setter (\<lambda>a. a(ptr := isa_setter (a ptr) v)))
                od"}
         $ (# isa_setter info) $ field_setter $ is_valid_struct 
       $ heap_setter   
  in
     make_getset_prop_gen [] cncl ctxt
  end
\<close>

ML \<open>
fun mk_getAsetB_prop (infoA : field_layout)(infoB : field_layout) ctxt : term =
  let
   val prms = [ ]
   val cncl = @{term "\<lambda> getter setter. getter (setter b v) = getter b"}
         $ (# isa_getter infoA) $ (# isa_setter infoB)
  in     
   make_getset_prop_gen prms cncl ctxt
  end
\<close>

(* analogous to mk_urecord_lems_for_uval *)
ML\<open> fun mk_getset_lems_for_rec file_nm ctxt name (infos : field_layout list) =
(* specialised-lemma generation for nth struct.*)
(* All uvals can reach this function. I have to filter them at some point.*)
 let
  
  val struct_C_nm = name;
  
  val _ = tracing ("mk_getset_lems_for_rec is generating lems for " ^ struct_C_nm)
  val heap            = Symtab.lookup (HeapInfo.get (Proof_Context.theory_of ctxt)) file_nm
                        |> Utils.the' "heap in mk_getset_lems_for_rec failed."
                        |> #heap_info;
  val struct_ty       = Syntax.read_typ ctxt struct_C_nm;
  val is_valid_struct = Typtab.lookup (#heap_valid_getters heap) struct_ty
             |> Utils.the' "is_valid_struct in take_member_default_mk_prog failed."
             |> Const;
   val heap_getter = Typtab.lookup (#heap_getters heap) struct_ty
             |> Utils.the' "heap_getter in take_member_default_mk_prog failed." |> Const
   val heap_setter = Typtab.lookup (#heap_setters heap) struct_ty
             |> Utils.the' "heap_getter in take_member_default_mk_prog failed." |> Const
       
  
  val (num_of_fields, field_names) = (List.length infos, List.map #name infos)
  val _ = tracing (@{make_string} (List.map #name infos))

  (* specialised_lemmas for each fields.
   * Three lemmas are generated if uval is of Writable.*)
  fun mk_lems_for_nth_field (field_num:int) =
   let
    val field_C_nm           = List.nth (field_names, field_num)
    val field_info           = List.nth (infos, field_num)
   in
    [{prop = mk_getdef_prop heap_getter is_valid_struct field_info ctxt,
      typ = GetDef, 
      name = # getter field_info ^ "_def_alt",
        mk_tactic = fn ctxt => custom_get_set_monadic_direct_tac ctxt 1 },
{prop = mk_setdef_prop heap_setter is_valid_struct field_info ctxt,
      typ = SetDef, 
      name = # setter field_info ^ "_def_alt",
        mk_tactic = fn ctxt => custom_get_set_monadic_direct_tac ctxt 1}
 ]
   end;

  fun mk_lems_for_nth_fields (field_numA:int) (field_numB:int)
    : getset_lem list =
   let
    val field_C_nmA           = List.nth (field_names, field_numA)
    val field_infoA           = List.nth (infos, field_numA)
    val field_C_nmB           = List.nth (field_names, field_numB)
    val field_infoB           = List.nth (infos, field_numB)
    val lem_name = name ^ "_get_" ^ field_C_nmA ^
                          "_set_" ^ field_C_nmB
    val lem = 
      if field_numA = field_numB then
        {prop = mk_getset_prop field_infoA ctxt, typ = GetSet, 
        name = lem_name,
        mk_tactic = fn ctxt => custom_get_set_same_field_tac ctxt 1}
      else
        {prop = mk_getAsetB_prop field_infoA field_infoB ctxt, 
        typ = GetASetB, 
        name = lem_name,
        mk_tactic = 
            fn ctxt => custom_get_set_different_field_tac ctxt 1}

   in
    [ lem  ]
   end;

  val lems1 = 
      List.tabulate (num_of_fields, fn field_numA =>
       List.tabulate (num_of_fields, fn field_numB  =>
       (let
        val _ = tracing ("  get o set for field numbers " ^ (Int.toString field_numA) ^
           " and " ^ (Int.toString field_numB))
       in
        mk_lems_for_nth_fields field_numA field_numB end))
       |> List.concat)

  val lems2 = 
        List.tabulate (num_of_fields, fn field_num => 
       (let
         val _ = tracing ("  get/set alternative def for field numbers " ^ (Int.toString field_num))
        in
         mk_lems_for_nth_field field_num end))

  val urecord_lems_for_nth_struct = 
    List.revAppend (lems1, lems2)
     |> List.concat 
     : getset_lem list;
 in
  urecord_lems_for_nth_struct : getset_lem list
 end;
\<close>

(* analogous to mk_lems *)
ML\<open> fun mk_getset_lems file_nm ctxt (* : {name : string, prop : term} *) =
 let
  val uvals = get_uvals file_nm (Proof_Context.theory_of ctxt) |> Utils.the' "mk_getset_lems"
  val names_infos =  uvals |> get_uval_custom_layout_records_no_redundancy
 (*  val uvals                 = read_table file_nm thy; *)
  val num_of_uvals          = List.length names_infos;
  fun get_nth_name_infos nth      = List.nth (names_infos, nth);
  val get_urecord_lems  = mk_getset_lems_for_rec file_nm ctxt;

  val (lemss:getset_lem list list) = List.tabulate (num_of_uvals, fn struct_num =>
     let
       val (name, infos) = get_nth_name_infos struct_num ;
     in  
     tracing ("mk_getset_lems started working for struct_number " ^ string_of_int struct_num ^
              " which corresponds to " ^ (*@{make_string}*) name);
    
     get_urecord_lems name infos  
    end) ;
 in
  List.concat lemss
  (* I don't know what does this part (copied from mk_lems) *)
(*
   |> map (fn v => (#name v, v))
   |> Symtab.make_list |> Symtab.dest
   |> map (fn (nm, xs) => let
       val fst_x = hd xs;
       val _ = map (fn x => (#prop x aconv #prop fst_x) orelse
             raise TERM ("lemmas: non duplicate for " ^ nm, [#prop x, #prop fst_x])) xs
       (* Why does Thomas want to have duplicate !? *)
      in hd xs end
    )*)
 end;
\<close>

ML \<open>


(* adapted from prove_put_in_bucket_non_esac_especialised_lemma *)
fun prove_put_in_bucket_getset_lemma (lem : getset_lem) lthy = 
   let
     val (lem_name, prop, mk_tac) = (#name lem, #prop lem, #mk_tactic lem);
     val _ = tracing ("Proving get/set lemma " ^ lem_name)
     (* We want to have schematic variables rather than fixed free variables after registering this lemma.*)
     val names = Variable.add_free_names lthy prop [];
     val some_thm = (SOME (Goal.prove lthy names [] prop (fn {context, prems} => (mk_tac context))))
                 handle ERROR err => (warning lem_name; warning err; NONE);
   (* If proof goes well, register the proved lemma and putting it in the corresponding bucket.
    * If not, add the name of the thm in Unborn_Thms. *)
      val lthy = case some_thm of
               SOME thm =>
                  Local_Theory.note ((Binding.name lem_name, []), [thm]) lthy |> snd |>
                  GetSetSimp.add_local thm
             | NONE => Local_Theory.target (add_unborns lem_name) lthy;
  in
     lthy
  end


\<close>

ML \<open>
(* adapted from local_setup_take_put_member_case_esac_specialised_lemmas *)
fun local_setup_getset_lemmas file_nm lthy =
 let
  val lems:getset_lem list = mk_getset_lems file_nm  lthy;
  val lthy''  = fold prove_put_in_bucket_getset_lemma lems lthy;
 in
  lthy''
 end;

\<close>


(* ***************


 Sanity checks for custom get/set-ters


************** *)


lemma test_and : " n < LENGTH('a) \<Longrightarrow> 
x && 2^n = y && 2^n \<Longrightarrow>
(((x :: ('a :: len)  word) !! n) = (y :: ('a :: len)  word) !! n)"
  apply(simp add:word_test_bit_def)
  apply uint_arith
  apply(simp add:uint_and uint_2p_alt bin_nth_eq_mod)
  by (metis (full_types) bin_nth_eq_mod bin_nth_ops(1) nth_2p_bin)


definition byKey :: "('a \<times> 'c) list \<Rightarrow> ('a \<times> 'c list) list"
  where "byKey l = 
 map (\<lambda> a. (a, map snd (filter (\<lambda>(a', _). a' = a) l)))
(remdups (map fst l))"

(* The first expression is more helpful when l is known since it can be computed.
*)
lemma list_ex_byKey : "list_ex (\<lambda> (a,b).p = a \<and> r \<notin> set b) (byKey l) = 
((\<exists> b. (p, b) \<in> set l) \<and> (p, r)\<notin> set l)"
  apply(simp flip:Bex_set)
  apply (simp add:byKey_def)  
  apply(simp add: Relation.fst_eq_Domain Relation.snd_eq_Range)
by blast

definition find_position :: "nat \<Rightarrow> nat \<Rightarrow> nat \<times> nat"
  where "find_position si offset  = (offset div si, offset mod si)"

(* Having twice the same definitions is useful to unfold specific occurences
in the goal rather than all of them 
*)
definition find_position' where "find_position' = find_position"
lemma find_position'_def' : "find_position' si offset  = (offset div si, offset mod si)"
  by (simp add:find_position'_def find_position_def)


lemma find_pos_le : "find_position n x = (p, r) \<Longrightarrow> 0 < n \<Longrightarrow> r < n "
  by(auto simp add:find_position_def)


lemma find_pos_case : "0 < q \<Longrightarrow> (\<And> p r. find_position q x = (p, r) \<Longrightarrow> r < q \<Longrightarrow> P (p,r)) \<Longrightarrow> P (find_position q x)"
  apply (cases "find_position q x")
  apply(simp add:find_position_def)  
  by auto

lemma find_pos_inj : " q > 0 \<Longrightarrow> x \<noteq> y \<Longrightarrow> find_position q x \<noteq> find_position q y"
  apply (simp add:find_position_def)
  apply(intro impI)  
  by (metis mod_by_0 mod_mult2_eq mult_0_right)
 
lemma find_pos_lt_notin :
" (x :: nat) < n \<Longrightarrow> 
x \<notin> set l \<Longrightarrow>
find_position q x = (p, r) \<Longrightarrow>
n mod q = 0 \<Longrightarrow>
0 < q \<Longrightarrow>
(p \<notin> set (map (fst o find_position' q) l) \<and> p < n div q) 
\<or> list_ex (\<lambda> (a,b).p = a \<and> r \<notin> set b) (byKey (map (find_position' q) l)) 
"
  apply(simp add:list_ex_byKey)  
  apply(rule excluded_middle[of "p \<notin> (\<lambda>x. fst (find_position' q x)) ` set l", THEN disjE])
  apply simp

apply(simp add: find_position'_def)   
   apply(intro conjI)  
  apply(simp add:find_position_def)
    apply blast
   apply (metis imageE find_pos_inj)
  apply simp  

  apply(simp add:find_position_def)
  
  by (metis diff_zero minus_mod_eq_div_mult td_gal_lt)


definition get_bit :: "(('a::len0) word)['n::finite] \<Rightarrow> nat \<Rightarrow> bool"
  where "get_bit arr pos = 
                (let (byte, off) = find_position LENGTH('a) pos in
                 arr.[byte] !! off )"

lemma power2_test : "x < LENGTH('a) \<Longrightarrow> n < LENGTH('a) \<Longrightarrow> ((((2 ^ x) :: ('a :: len)  word) !! n) = (x = n))"
  apply(simp add:nth_shiftl flip:shiftl_1)
  by(unat_arith)

definition size_of_arr_bits :: "(('a::len0) word)['n::finite] \<Rightarrow> nat"
  where "size_of_arr_bits _ = LENGTH('a)*CARD('n)"





 







ML \<open>
fun getter_sanity_tac ctxt = 
 let
    val gets = Proof_Context.get_thms ctxt
    val get  = Proof_Context.get_thm ctxt
  in
 K (print_tac ctxt "Getter sanity lemma")
THEN' 
 (asm_full_simp_tac (ctxt addsimps [get "find_position_def", get "get_bit_def"])
THEN'
 (fn i => 
TRY (REPEAT_ALL_NEW (eresolve_tac ctxt @{thms exE conjE}) i))
(* THEN' K (print_tac ctxt "coucou") *)
THEN' custom_get_set_different_field_tac ctxt
) end
\<close>



ML \<open>
fun setter_sanity_tac ctxt = 
 let
    val gets = Proof_Context.get_thms ctxt
    val get  = Proof_Context.get_thm ctxt
  in
  K (print_tac ctxt "Setter sanity lemma")
THEN' asm_full_simp_tac ((clear_simpset ctxt) addsimps [get "get_bit_def"]) 
THEN' rtac (get "find_pos_case")  THEN' asm_full_simp_tac ctxt 
 THEN' dresolve_tac ctxt (gets "find_pos_lt_notin") 
THEN' assume_tac ctxt THEN' assume_tac ctxt
(* each one should discharge a goal *)
THEN' asm_full_simp_tac (ctxt addsimps [get "size_of_arr_bits_def"]) 
THEN' asm_full_simp_tac ctxt
(* speed up : eliminate one assumption *)
THEN' Rule_Insts.thin_tac ctxt "x \<notin> set _" [] 
THEN' asm_full_simp_tac (ctxt addsimps [get "find_position'_def'", get "size_of_arr_bits_def", get "byKey_def"]) 
THEN' rtac (get "test_and")
THEN' asm_full_simp_tac ctxt (* discharge *)
THEN'
K (TRY ( Method.elim ctxt  [ get "disjE"]  []
 |> Method.NO_CONTEXT_TACTIC ctxt))
 THEN_ALL_NEW 
( (* eliminate inconsistent contexts *)
Lin_Arith.tac ctxt  ORELSE'
custom_get_set_different_field_tac (ctxt addsimps [get "power2_test"]))

 end
\<close>  

ML \<open>
fun prove_thm ctxt assms concl tactic = 
let
val clean = HOLogic.mk_Trueprop o strip_atype
val thm0 = mk_meta_imps (map clean assms) (concl |> clean) ctxt
val names =  Variable.add_free_names ctxt thm0 []
in
Goal.prove ctxt names [] thm0
( fn {context, prems} => tactic context 1)
end
\<close>

ML \<open>
fun make_getter_sanity_thm ctxt data_get layfield (field_info : field_layout) = 
let
val ass = 
  @{term 
  "\<lambda>  lay data. 
   (\<forall> x\<in> set(layout_taken_bit_list lay). 
  get_bit (data s) x = get_bit (data t) x)
  "
  } $ layfield $ data_get
val concl = @{term "\<lambda> getter . getter s = getter t"  }
        $ # isa_getter field_info
in
prove_thm ctxt [ass] concl getter_sanity_tac
end

\<close>
ML \<open>
fun make_setter_sanity_thm ctxt data_get layfield (field_info : field_layout) = 
let

val ass1 = 
  @{term 
  "\<lambda>  data .x < size_of_arr_bits (data s) 
  "
  } $ data_get
val ass2 = 
  @{term 
  "\<lambda>  lay .x \<notin> set (layout_taken_bit_list lay) 
  "
  } $ layfield
val concl = @{term "\<lambda> data setter . 
   get_bit (data (setter s b)) x = get_bit (data s) x"  }
        $ data_get
        $ # isa_setter field_info
in
prove_thm ctxt [ass1, ass2] concl setter_sanity_tac 
end
\<close>

ML \<open>
fun make_getset_sanity_thms ctxt (Ctyp, lay) : ((string * thm) * (string * thm)) list =
let
val data_get = Ctyp ^ ".data_C" |> Syntax.read_term ctxt
val (info, lays) = 
case lay of
CustomLayout (info, 
Const ("Option.option.Some", _) $ 
( Const ("Cogent.ptr_layout.LayRecord", _) $ 
layout)) => 
(info, 
layout |> HOLogic.dest_list
|> map HOLogic.dest_prod
|> map (apfst HOLogic.dest_string)
|> Symtab.make
)
in
map (
fn field => 
let val lay = Symtab.lookup lays (# name field) |> the 
val prefix = Ctyp ^ "_" ^ #name field 
in
((prefix ^ "_getter_sanity", make_getter_sanity_thm ctxt data_get lay field),
(prefix ^ "_setter_sanity", make_setter_sanity_thm ctxt data_get lay field))
end
) 
 info

end
\<close>


ML \<open>

fun local_setup_getset_sanity_lemmas file_nm lthy =
 let
  val uvals =  get_uvals file_nm (Proof_Context.theory_of lthy) |> Utils.the' "local_setup_getset_sanity_lemmas"
    |> get_uval_custom_layout_records   
    |> List.map (fn x => (get_ty_nm_C x, get_uval_layout x)) |> rm_redundancy
  
  val (get_thms, set_thms) = List.map (make_getset_sanity_thms lthy) uvals
      |> List.concat |> ListPair.unzip
  val thms = get_thms @ set_thms
  
  fun add_to_bucket (name, thm) lthy  = 
  Local_Theory.note ((Binding.name name, []), [thm]) lthy |> snd |>
                  GetSetSanity.add_local thm
  val lthy''  = fold add_to_bucket thms lthy;
 in
  lthy''
 end;

\<close>


(*  **********

The remaining of this file is devoted to the correctness of custom getters (that of custom setters
is deduced from get/set lemmas, i.e., by the fact that they are inverse to getters).

The main definition is uval_from_array which is roughly a specification of getters.

************** *)

fun sized_word_from_array' :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> (('a::len) word)['n::finite] \<Rightarrow> ('b :: len) word"
  where "sized_word_from_array' byte 0 bito ar = (ucast (ar.[byte])  && mask bito)"
  | "sized_word_from_array' byte (Suc byteo) bito ar = ucast (ar.[byte]) || (sized_word_from_array' (Suc byte) byteo bito ar << LENGTH('a)) "

(* first argument: offset, second argument size  *)
definition sized_word_from_array :: "nat \<Rightarrow> nat \<Rightarrow> (('a::len) word)['n::finite] \<Rightarrow> ('b :: len) word"
  where "sized_word_from_array pos s ar = 
          (let (bytei, offi) = find_position LENGTH('a) pos in
           let (bytee, offe) = find_position LENGTH('a) (pos + s) in           
            if bytei = bytee then
             ucast ((ar.[bytei] >> offi) && mask (offe - offi))
           else 
             ((ucast ((ar.[bytei] >> offi))
\<comment> \<open> this mask is not necessary, but it matches the haskell implementation of get/set-ers\<close>
&& mask (LENGTH('a) - offi)
  )
               || (sized_word_from_array' (Suc bytei) (bytee - bytei - 1) offe ar << (LENGTH('a) - offi)))               
)"


definition word_from_array :: "nat \<Rightarrow> (('a::len) word)['n::finite] \<Rightarrow> ('b :: len) word"
  where "word_from_array pos ar = sized_word_from_array pos LENGTH('b) ar"


(* Ensures that in a data array, tag values are among the specified ones in the layout.

TODO: add this condition to the value relation to compensate for its laziness. Indeed,
consider a variant with two constructors A and B, where the tag is either 0 or 2. 
The value relation only enforces that if the tag
is 0 and then the update value must be A, otherwise it is B. This is because the generated getter
only tests whether the tag is 0, implicitly assuming that if not it must be 2, and not 3, for example.
 As a consequence, the value relation is weaker than expected. Adding the following condition to the value relation
would solve this issue.

We assume for simplicity that the tag fits on 32 words.

 *)
fun valid_tags :: "ptr_layout \<Rightarrow> (('a::len) word)['n::finite] \<Rightarrow> bool"
  where 
  "valid_tags (LayVariant (s, n) ls) a = (\<exists> (_, tag, l) \<in> set ls. ((of_nat tag :: 32 word) = sized_word_from_array n s a \<and> valid_tags l a))"
| "valid_tags (LayRecord ls) a = (\<forall> (_, l) \<in> set ls. (valid_tags l a))"
| "valid_tags (LayProduct l1 l2 ) a = (valid_tags l1 a \<and> valid_tags l2 a)"
| "valid_tags (LayVar _ _) _ = True"
| "valid_tags (LayBitRange _ _) _ = True"

definition get_name_layout 
where get_name_layout_def : "get_name_layout   =  (\<lambda> n s a ls. 
  let (name, _, l) = the (find (\<lambda> (_, v, _). of_nat v = (sized_word_from_array n s a :: 32 word)) ls)
in (name, l))"

(* 

Endianness

*)


(*
is_reverse_of v v' means that v and v' represent the same value with opposite
endianness (i.e., one is the reverse of the other, as a list of bytes)
*)
definition is_reverse_of :: "('a :: len0) word \<Rightarrow> 'a word \<Rightarrow> bool"
  where "is_reverse_of v v' =
 (\<forall> p < (LENGTH('a) div 8). (v >> (p * 8)) && 0xFF = (v' >> (LENGTH('a) - (p + 1) * 8)) && 0xFF)"


(* Following the definition of swap_u8 in cogent-endianness.h *)
definition swap_u8 :: " 8 word \<Rightarrow> 8 word" 
  where "swap_u8 v = v"


(* swap does indeed reverse *)
lemma "is_reverse_of v (swap_u8 v)"
  apply (simp add:swap_u8_def is_reverse_of_def)
  done


(* Following the definition of swap_u16 in cogent-endianness.h *)
definition swap_u16 :: " 16 word \<Rightarrow> 16 word" 
  where "swap_u16 v = ((v << 8) || (v >> 8))"


(* swap does indeed reverse *)
lemma "is_reverse_of v (swap_u16 v)"
  apply (simp add:swap_u16_def is_reverse_of_def)
  apply (intro allI impI)
  apply (case_tac p; simp) 
  apply word_bitwise_signed+
  done

(* following the definition of swap_u32 in cogent-endianness.h *)
definition swap_u32 :: "32 word \<Rightarrow> 32 word" 
  where swap_u32_def[simplified HOL.Let_def]:
  "swap_u32 v = (let v' = ((v << 8) && 0xFF00FF00) ||  ((v >> 8) && 0xFF00FF)
in 
(v' << 16) || (v' >> 16))"


(* swap does indeed reverse *)
lemma "is_reverse_of v (swap_u32 v)"
  apply (simp add:swap_u32_def is_reverse_of_def)
  apply (intro allI impI)
  apply (case_tac p; clarsimp) 
   apply word_bitwise_signed
  apply(rename_tac p)
  apply (case_tac p; clarsimp) 
   apply word_bitwise_signed
  apply(rename_tac p)
  apply (case_tac p; clarsimp)
  apply word_bitwise_signed+
done


(* following the definition of swap_u64 in cogent-endianness.h *)
definition swap_u64 :: "64 word \<Rightarrow> 64 word" 
  where swap_u64_def[simplified HOL.Let_def]:
  "swap_u64 v = (
 let v = ((v << 8) && 0xFF00FF00FF00FF00) || ((v >> 8) && 0x00FF00FF00FF00FF) in
 let  v = ((v << 16) && 0xFFFF0000FFFF0000) || ((v >> 16) && 0x0000FFFF0000FFFF) in
   (v << 32) || (v >> 32)
)"


(* swap does indeed reverse *)
lemma "is_reverse_of v (swap_u64 v)"
  apply (simp add:swap_u64_def is_reverse_of_def)
  apply (intro allI impI)
  apply (case_tac p; clarsimp)
   apply word_bitwise_signed
  apply(rename_tac p)
  apply (case_tac p; clarsimp) 
   apply word_bitwise_signed
  apply(rename_tac p)
  apply (case_tac p; clarsimp)
   apply word_bitwise_signed
  apply(rename_tac p)
  apply (case_tac p; clarsimp)
   apply word_bitwise_signed
  apply(rename_tac p)
  apply (case_tac p; clarsimp)
   apply word_bitwise_signed
  apply(rename_tac p)
  apply (case_tac p; clarsimp)
   apply word_bitwise_signed
  apply(rename_tac p)
  apply (case_tac p; clarsimp)
   apply word_bitwise_signed+
  done



lemmas reverse_word8_lems = swap_u8_def swap_u16_def swap_u32_def swap_u64_def

(* We assume a little endian architecture, following AutoCorres. *)
fun endianize :: "(('a :: len) word \<Rightarrow> 'a word) \<Rightarrow> 'a word \<Rightarrow> Endianness \<Rightarrow> 'a word"
  where 
    "endianize _ w ME = w"
  | "endianize _ w LE = w" 
  | "endianize swap w BE  = swap w" 


 

(* 

Construct a value in the update semantics of the given type according to the layout, out of a given
word array.

Since the value relation involves them, proving that generated getters and setters are correct means 
proving that the constructed value relates to the original word array,
typically:

valid_tags (layout_from_trecord type) (data_C t) \<Longrightarrow>  val_rel (uval_from_array_toplevel type (data_C t)) t"

*)
fun uval_from_array :: "ptr_layout \<Rightarrow> type \<Rightarrow> (('a::len) word)['n::finite] \<Rightarrow> (char list, 'b, 32 word) uval"
  where "uval_from_array (LayRecord ls) (TRecord ts Unboxed) a = 
              URecord (map (\<lambda> (n, t, _). 
                      let l = assoc ls n in
                        (uval_from_array l t a, type_repr t))
                   ts) None" 
  | "uval_from_array (LayBitRange (_, n) e) (TRecord ts (Boxed rw ptrl)) a = UPtr (endianize swap_u32 (word_from_array n a) e) (type_repr ((TRecord ts (Boxed rw ptrl)))) "
  | "uval_from_array (LayBitRange (_, n) e) (TPrim (Num U8)) a = UPrim (LU8 (endianize swap_u8 (word_from_array n a) e )) "
  | "uval_from_array (LayBitRange (_, n) e) (TPrim (Num U16)) a = UPrim (LU16 (endianize swap_u16 (word_from_array n a) e)) "
  | "uval_from_array (LayBitRange (_, n) e) (TPrim (Num U32)) a = UPrim (LU32 (endianize swap_u32 (word_from_array n a) e)) "
  | "uval_from_array (LayBitRange (_, n) e) (TPrim (Num U64)) a = UPrim (LU64 (endianize swap_u64 (word_from_array n a) e)) "
  | "uval_from_array (LayBitRange (s, n) e) (TCustomNum _) a = 
                                   UCustomInt s (
                                   if n > 32 then
                                      unat (sized_word_from_array n s a :: 64 word)
                                   else
                                      unat (sized_word_from_array n s a :: 32 word)
                                    ) " 
  | "uval_from_array (LayBitRange (_, n) e) (TPrim Bool) a = UPrim (LBool (get_bit a n)) "
  | "uval_from_array _ TUnit a = UUnit "
  | uval_from_array_variant: 
  (* the variant case is a bit convoluted because it must satisfy Isabelle termination checker.
Below, an alternative equivalent definition is provided (see uval_from_array_variant')
*)
   "uval_from_array (LayVariant (s, n) ls) (TSum ts) a =
(    
let rts = map (\<lambda>(n, t, _). (n, type_repr t)) ts in
let name_l = get_name_layout n s a ls in
let name = fst name_l in
let l = snd name_l in
    let m =  List.map (\<lambda> (n, t, _) .  
       if n = name then Some 
         (uval_from_array l t a)
\<comment> \<open>(* N'y a t'il pas un pb pour le tag si il ne fait pas une size standard? *)\<close>
\<comment> \<open>(USum n (uval_from_array l t a) rts)\<close>
  else None

) ts in
USum name ( case (List.find (\<lambda> x. \<not> (Option.is_none x)) m) of Some (Some x) \<Rightarrow> x ) 
rts)
 "


declare uval_from_array_variant[simp del]

lemma uval_from_array_variant' :
  "let rts = map (\<lambda>(n, t, _). (n, type_repr t)) ts in
   let name_l = get_name_layout n s a ls in
   let name = fst name_l in
   let l = snd name_l in
   let v = case (find (\<lambda> (n, _, _). n = name) ts) of
     Some (_,t,_) \<Rightarrow> uval_from_array l t a 
   in
     uval_from_array (LayVariant (s, n) ls) (TSum ts) a = USum name v rts"
proof -
  {
    fix p f l 
    have " find p (map f l) = option_map f ( find (p o f) l)"
      by(induct l;simp)
  }
  note find_map = this

  have eq: "\<And> name machin. (\<lambda>x. \<not> Option.is_none
                              (case x of
                               (n, t, _) \<Rightarrow>
                                 if n =  name then Some (machin t)
                                 else None)) =
    (\<lambda>(n, t, _) \<Rightarrow> n =  name)"
    apply(rule ext)
    apply(simp split:prod.split)
    done

  show ?thesis

    apply (simp add:uval_from_array_variant Let_def)
    apply(simp add:find_map comp_def)
    apply(subst eq)
    apply(cases "(find (\<lambda>(na, _, _). na = fst (get_name_layout n s a ls)) ts)") 
     apply(simp)   
    apply simp
    apply (simp split:prod.split)  
    apply(intro allI impI)
    apply(drule findSomeD)
    by fast
qed

(* 
A helper to prove correctness of get/set-ters, variant case.

The idea is to put the "let..in" at the top level so that alternatives
become a cunjunction of possibilites to be shown.
*)
lemma corres_getter_variant :
  assumes 
    "distinct (map fst ts)"
    " \<comment> \<open>the distinct hypothesis helps simplification tactics\<close>
     distinct (map fst ts)
     \<Longrightarrow>
    let rts = map (\<lambda>(n, t, _). (n, type_repr t)) ts in
    let name_l = get_name_layout n s a ls in
    let name = fst name_l in
    let l = snd name_l in
    let v = case (find (\<lambda> (n, _, _). n = name) ts) of
      Some (_,t,_) \<Rightarrow> uval_from_array l t a 
    in
     val_rel (USum name v rts) x"
  shows 
    "val_rel (uval_from_array (LayVariant (s, n) ls) (TSum ts) a) x"
 
    using assms
    using uval_from_array_variant'
    by metis


fun uval_from_array_toplevel :: " type \<Rightarrow> (('a::len) word)['n::finite] \<Rightarrow> (char list, 'b, 32 word) uval"
where "uval_from_array_toplevel  (TRecord ts (Boxed _ (Some (LayRecord ls)))) a = 
              URecord (map (\<lambda> (n, t, _). 
                      let l = assoc ls n in
                        (uval_from_array l t a, type_repr t))
                   ts) (Some (LayRecord ls))"

fun layout_from_trecord :: "type \<Rightarrow> ptr_layout"
  where "layout_from_trecord (TRecord l (Boxed _ (Some ptrl))) = ptrl"


(* Adapted from term_to_string found on the Isabelle mailing list (makarius) 
The bare Syntax.string_of_term sometimes returns "<markup>" instead of the real stuff
*)
ML \<open>
  fun typ_to_string ctxt t =
    let
      val ctxt' = Config.put show_markup false ctxt;
    in Print_Mode.setmp [] (Syntax.string_of_typ ctxt') t end;
\<close>

ML \<open>
local

(* 
Suppose the current subgoal is .. \<Longrightarrow> val_rel t1 t2 = .. .
This function returns the type of t2, stringified.
*)
fun get_val_rel_type ctxt thm : string = 

  let 
    val concl = Thm.major_prem_of thm (* may fail *)
  in

   (case concl |> Utils.lhs_of_eq of
     _ $ _ $ t => t |> Thm.cterm_of ctxt |>   Thm.typ_of_cterm  
                    |> typ_to_string ctxt 
           | _ => "" ) 
    handle TERM ("lhs_of_eq", _) => ""
end
  handle THM(_, _, _) => ""
in
(* 
Suppose the current subgoal is .. \<Longrightarrow> val_rel t1 t2 = ..,
where t2 is of type A.
This tactic tries to apply val_rel_A_def, if it exists.

*)
fun apply_val_rel_def ctxt i : tactic = fn thm =>
let 
  val vrel = get_val_rel_type ctxt thm 
  val th_name = "val_rel_" ^ vrel ^ "_def"   
  val th = (Proof_Context.get_thms ctxt th_name) handle _ => [] (* theorem may not exist *)
in  
   resolve_tac ctxt th i thm

end

end
\<close>

ML \<open>

(*
Suppose the current subgoal is .. \<Longrightarrow> val_rel x1 t1.

This tactic performs one unfolding of val_rel with the following attempted results in order:
1. corres_getter_variant
2. ValRelSimp
3. val_rel_A_def, where A is the type of t1

The third case may be ussed at top level only. Indeed, it seems ValRelSimp may not include the definition
of some value relation if the type is not involved as a subfield somewhere.


*)
fun unfold1_val_rel ctxt = 
  let
    val gets = Proof_Context.get_thms ctxt
    val tags = gets "tag_t_defs" handle ERROR _ => []    
    val val_rels   = ValRelSimp.get ctxt;
  in
  (resolve_tac ctxt @{thms  corres_getter_variant[simplified Let_def]}
   ORELSE'  
   (resolve_tac ctxt @{thms HOL.iffD2} 
     THEN' resolve_tac ctxt @{thms HOL.meta_eq_to_obj_eq}
     THEN' (resolve_tac ctxt val_rels
            ORELSE' 
            apply_val_rel_def ctxt)  
   ))

  (* doing a first simplification without any simpset seems helpful *)
  THEN_ALL_NEW (fn i => TRY (asm_full_simp_tac ctxt i))
  THEN_ALL_NEW
     (fn i => TRY (asm_full_simp_tac (ctxt addsimps tags addsimps
       
    @{thms get_name_layout_def word_from_array_def sized_word_from_array_def 
         find_position_def ucast_id mask_def } ) i))
end


fun val_rel_split ctxt  = 
    unfold1_val_rel ctxt 
 THEN_ALL_NEW
    (fn i => TRY (REPEAT_ALL_NEW (resolve_tac ctxt @{thms impI conjI}) i))
 

(* 

Recursively simplify a goal .. \<Longrightarrow> val_rel by unfolding it

*)
fun recursive_val_rel_split ctxt = REPEAT_ALL_NEW (val_rel_split ctxt)


(* 

proves correctness of getters, i.e., a goal of the form
valid_tags (layout_from_trecord type) (data_C t) \<Longrightarrow>  val_rel (uval_from_array_toplevel type (data_C t)) t

*)
fun solve_corres_getters ctxt0 = 
let
  val ctxt = ctxt0 addsimps @{thms reverse_word8_lems
    (* for custom sized int *)
      mask_def unat_ucast_mask}
  val gets = Proof_Context.get_thms ctxt
  val tags = gets "tag_t_defs" handle ERROR _ => []
in
  asm_full_simp_tac (ctxt addsimps
   @{thms word_from_array_def find_position_def mask_def sized_word_from_array_def ucast_id})
  THEN'  recursive_val_rel_split ctxt 
  THEN_ALL_NEW (fn i => TRY (asm_full_simp_tac (ctxt addsimps 
         GetSetDefs.get ctxt addsimps tags addsimps @{thms get_bit_def find_position_def}) i))
  THEN_ALL_NEW
      (fn i => TRY (asm_full_simp_tac (Raw_Simplifier.flip_simp @{thm One_nat_def} ctxt) i))
  THEN_ALL_NEW
      bw_tac_signed ctxt
end
\<close>


ML \<open>

fun make_getter_correctness_thms ctxt (Ctyp, cog_type) : (string * thm)  =
let
val data_get = Ctyp ^ ".data_C" |> Syntax.read_term ctxt
val ass = @{term "\<lambda> type data . valid_tags (layout_from_trecord type) (data t)"}
   $ cog_type $ data_get
val concl = @{term "\<lambda> type data . val_rel (uval_from_array_toplevel type (data t)) t"}
  $ cog_type $ data_get
val name = Ctyp ^ "_getter_correct"
val _ = tracing ("Proving " ^ name)
in
(name, prove_thm ctxt [ass] concl solve_corres_getters)

end
(*
val (info, lays) = 
case lay of
CustomLayout (info, 
Const ("Option.option.Some", _) $ 
( Const ("Cogent.ptr_layout.LayRecord", _) $ 
layout)) => 
(info, 
layout |> HOLogic.dest_list
|> map HOLogic.dest_prod
|> map (apfst HOLogic.dest_string)
|> Symtab.make
)

val ass = 
  @{term 
  "\<lambda>  lay data. 
   (\<forall> x\<in> set(layout_taken_bit_list lay). 
  get_bit (data s) x = get_bit (data t) x)
  "
  } $ layfield $ data_get
val concl = @{term "\<lambda> getter . getter s = getter t"  }
        $ # isa_getter field_info
in
prove_thm ctxt [ass] concl getter_sanity_tac
*)

(*
map (
fn field => 
let val lay = Symtab.lookup lays (# name field) |> the 
val prefix = Ctyp ^ "_" ^ #name field 
in
((prefix ^ "_getter_sanity", make_getter_sanity_thm ctxt data_get lay field),
(prefix ^ "_setter_sanity", make_setter_sanity_thm ctxt data_get lay field))
end
) 
 info *)


\<close>
ML \<open>
fun local_setup_getter_correctness file_nm lthy =
 let
  val uvals =  get_uvals file_nm (Proof_Context.theory_of lthy) |> Utils.the' "local_setup_getter_correctness"
    |> get_uval_custom_layout_records   
    |> rm_redundancy_by (fn x => (get_ty_nm_C x, get_uval_layout x))
    |> List.map (fn x => (get_ty_nm_C x, get_uval_typ x)) 
    (* |> @{print} *)

  val thms = List.map (make_getter_correctness_thms lthy) uvals
  
  
  fun add_to_bucket (name, thm) lthy  = 
  Local_Theory.note ((Binding.name name, []), [thm]) lthy |> snd |>
                  GetSetSanity.add_local thm
  val lthy''  = fold add_to_bucket thms lthy;
 in
  lthy''
 end;

\<close>


end
