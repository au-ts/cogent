(*
 * Copyright 2018, Data61
 * Commonwealth Scientific and Industrial Research Organisation (CSIRO)
 * ABN 41 687 119 230.
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(DATA61_GPL)
 *)

theory ProofTrace
  imports
    Main
    "ML_Old"
begin

(* begin: tactic trace code *)
(* Proof of concept implementation. DO NOT USE THIS CODE *)
ML {*
datatype 'tag Step = Step of ('tag * tactic * int)

datatype SolveTacFailure =
    SolveTac_DepthExceeded (* depth_limit reached 0 *)
  | SolveTac_ProofFailed   (* nested TraceFailure gives reason *)

datatype 'tag TraceSuccess = TraceSuccess of { goal : thm
                                             , theorem : thm
                                             , subproofs : 'tag TraceSubgoal list
                                             }
     and 'tag TraceFailure = TraceFailure of { goal : thm
                                             , succeeded : 'tag TraceSubgoal list
                                             , failed : { subgoal : thm
                                                        , fail_steps : { step : 'tag Step
                                                                       , trace : 'tag TraceFailure
                                                                       } list
                                                        , fail_reason : SolveTacFailure
                                                        }
                                             , remaining_goals : term list
                                             }
     and 'tag TraceSubgoal = TraceSubgoal of { subgoal : thm
                                             , subtheorem : thm
                                             , fail_steps : { step : 'tag Step
                                                            , trace : 'tag TraceFailure
                                                            } list
                                             , step : 'tag Step
                                             , subproof : 'tag TraceSuccess
                                             }

fun TraceSuccess_erase_backtracking (TraceSuccess { goal = goal, theorem = theorem, subproofs = subproofs }) =
      TraceSuccess { goal = goal, theorem = theorem, subproofs = map TraceSubgoal_erase_backtracking subproofs }
and TraceFailure_erase_backtracking (TraceFailure trace) =
      TraceFailure { goal = #goal trace
                   , succeeded = #succeeded trace |> map TraceSubgoal_erase_backtracking
                   , failed = { subgoal = #failed trace |> #subgoal
                              , fail_steps = #failed trace |> #fail_steps |> take 1
                                             |> map (fn fs => { step = #step fs
                                                              , trace = #trace fs |> TraceFailure_erase_backtracking })
                              , fail_reason = #failed trace |> #fail_reason
                              }
                   , remaining_goals = #remaining_goals trace
                   }
and TraceSubgoal_erase_backtracking (TraceSubgoal trace) =
      TraceSubgoal { subgoal = #subgoal trace
                   , subtheorem = #subtheorem trace
                   , fail_steps = []
                   , step = #step trace
                   , subproof = #subproof trace |> TraceSuccess_erase_backtracking
                   }
*}

ML {*
datatype ('l, 'r) Either = Left of 'l | Right of 'r

fun mapEither fl _ (Left l) = Left (fl l)
  | mapEither _ fr (Right r) = Right (fr r)

fun mapEitherL f e = mapEither f (fn x => x) e
fun mapEitherR f e = mapEither (fn x => x) f e
*}

ML {*
fun findIndex p =
  let fun find _ [] = NONE
        | find n (x::xs) = if p x then SOME (x, n) else find (n+1) xs
  in find 0 end
fun zipWith _ [] _ = []
  | zipWith _ _ [] = []
  | zipWith f (x::xs) (y::ys) = f x y :: zipWith f xs ys
fun isSome (SOME _) = true
  | isSome _ = false
fun enumerate xs = let
  fun enum _ [] = []
    | enum n (x::xs) = (n, x) :: enum (n+1) xs
  in enum 0 xs end
fun nubBy _ [] = []
  | nubBy f (x::xs) = x :: filter (fn y => f x <> f y) (nubBy f xs)
*}

ML {*
(* generalised Term.lambda *)
fun my_lambda args =
  let val n = length args
      fun lambda' depth args t =
        (case findIndex (fn (a, _) => a = t) args of
            NONE =>
              (case t of
                  f $ x => lambda' depth args f $ lambda' depth args x
                | Abs (v, typ, t) => Abs (v, typ, lambda' (depth + 1) (map (apfst (incr_boundvars 1)) args) t)
                | Bound k => if k >= depth then Bound (k + n) else Bound k
                | _ => t)
          | SOME (_, k) => Bound (k + depth))
  in lambda' 0 (rev args)
     #> fold (fn (_, (name, typ)) => fn t => Abs (name, typ, t)) (rev args)
  end

fun subterm_type absvars t = let
  fun subst absvars (Bound k) = Free (nth absvars k)
    | subst absvars (f $ x) = subst absvars f $ subst absvars x
    | subst absvars (Abs (v, typ, t)) = Abs (v, typ, subst ((v, typ) :: absvars) t)
    | subst _ t = t
  in fastype_of (subst absvars t) end
fun my_typ_insts (Type (_, args)) (Type (_, args')) =
    if length args <> length args' then NONE else
    let val instss = zipWith my_typ_insts args args'
    in if exists (not o isSome) instss then NONE else
         SOME (List.mapPartial I instss |> List.concat) end
  | my_typ_insts (TFree _) (TFree _) = SOME []
  | my_typ_insts (TVar tv) typ = SOME [(tv, typ)]
  | my_typ_insts _ _ = NONE
fun my_typ_match' absvars (t as f $ x) t' =
      (case strip_comb t of
          (Var _, _) => my_typ_insts (subterm_type absvars t) (subterm_type absvars t')
        | _ => (case t' of
                   f' $ x' => (case (my_typ_match' absvars f f', my_typ_match' absvars x x') of
                                  (SOME fmatch, SOME xmatch) => SOME (fmatch @ xmatch)
                                | _ => NONE)
                 | _ => NONE))
  | my_typ_match' absvars (Abs (_, typ, t)) (Abs (v', typ', t')) =
      (case (my_typ_insts typ typ', my_typ_match' ((v', typ') :: absvars) t t') of
          (SOME absmatch, SOME tmatch) => SOME (absmatch @ tmatch)
        | _ => NONE)
  | my_typ_match' absvars t t' = case my_typ_insts (subterm_type absvars t) (subterm_type absvars t') of
       SOME x => SOME x
     | NONE => raise TYPE ("my_typ_insts fail", [subterm_type absvars t, subterm_type absvars t'], [t, t'])
fun my_typ_match t t' = my_typ_match' [] (Envir.beta_norm t) t'
                        handle TYPE (msg, typs, terms) => raise TYPE (msg, typs, terms @ [t, t'])

fun annotate_boundvar _ absvars (Bound n) =
      if n < length absvars then (Bound n, nth absvars n)
        else raise TYPE ("annotate_boundvar", map snd absvars, [Bound n])
  | annotate_boundvar _ _ (t as Free (name, typ)) = (t, (name, typ))
  | annotate_boundvar i absvars t = (t, ("var" ^ Int.toString i, subterm_type absvars t))
fun my_match' _ (Var v) t' = SOME [(v, [], t')]
  | my_match' absvars (t as f $ x) t' =
      (case strip_comb t of
          (Var v, args) => SOME [(v, map (fn (i, arg) => annotate_boundvar i absvars arg)
                                             (enumerate args), t')]
        | _ => (case t' of
                   f' $ x' => (case (my_match' absvars f f', my_match' absvars x x') of
                                  (SOME uf, SOME ux) => SOME (uf @ ux)
                                | _ => NONE)
                 | _ => NONE))
  | my_match' absvars (Abs (name, typ, t)) (Abs (_, typ', t')) =
      if typ = typ' then my_match' ((name, typ)::absvars) t t' else NONE
  | my_match' absvars t t' = if t = t' then SOME [] else NONE
fun my_match t t' = my_match' [] (Envir.beta_norm t) t'

fun my_unify_fact_tac ctxt subproof n state =
  let val cterm_of' = Thm.cterm_of ctxt
      val ctyp_of' = Thm.ctyp_of ctxt
  in
  if length (Thm.prems_of state) < n then no_tac state else
  let val stateterm = nth (Thm.prems_of state) (n-1)
      val proofterm = Thm.prop_of subproof
  in
  case my_typ_match stateterm proofterm of
     NONE => Seq.empty
   | SOME typinsts =>
     (case Thm.instantiate (map (fn (v, t) => (v, ctyp_of' t)) (nubBy fst typinsts), []) state of
       state' =>
        let val stateterm' = nth (Thm.prems_of state') (n-1) in
        case my_match stateterm' proofterm of
           NONE => Seq.empty
         | SOME substs =>
             let val substs' = nubBy #1 substs
                               |> map (fn (var, args, t') => (var, my_lambda args t'))
                               |> map (fn (v, t) => (v, cterm_of' t))
             in
             case Thm.instantiate ([], substs') state of state' =>
               (case Proof_Context.fact_tac ctxt [gen_all 1 subproof] 1 state' |> Seq.pull of
                   NONE => Seq.empty
                 | r => Seq.make (fn () => r))
             handle _ => Seq.empty
             end
       handle _ => Seq.empty
      end)
      handle _ => Seq.empty
  end
  end
*}

ML {*
fun trace_solve_tac (ctxt : Proof.context)
                    (backtrack : bool)
                    (get_tacs : 'data -> term -> ('data * 'tag * tactic) list)
                    (data0 : 'data) (goal0 : thm)
                    (depth_limit : int option)
                    : 'data * ('tag TraceFailure, 'tag TraceSuccess) Either =
  let val cterm_of' = Thm.cterm_of ctxt
      val option_decr = Option.map (fn x => x - 1)
      val subgoals0 = Thm.prems_of goal0
  in
  if null subgoals0 then (data0, TraceSuccess { goal = goal0, theorem = goal0, subproofs = [] } |> Right) else
  if depth_limit = SOME 0 then
      (data0, TraceFailure { goal = goal0
                           , succeeded = []
                           , failed = { subgoal = (Goal.init (cterm_of' (hd subgoals0)))
                                      , fail_steps = []
                                      , fail_reason = SolveTac_DepthExceeded
                                      }
                           , remaining_goals = tl subgoals0
                           } |> Left)
  else let
    fun solve data goal subproofs_rev =
        case Thm.prems_of goal of
            [] => (data, TraceSuccess { goal = goal0, theorem = goal, subproofs = rev subproofs_rev }
                         |> Right)
          | (subgoal_term::remaining_subgoals) =>
               let (* Try all results from all tactics until we obtain a successful proof.
                    * NB: tactics should return finite results! *)
                 val subgoal = Goal.init (cterm_of' subgoal_term)
                 fun try_tacs [] fails = (data, Left fails)
                   | try_tacs ((data, tag, tactic) :: rest) fails = let
                       fun try_results n r fails = case Seq.pull r of
                             NONE => try_tacs rest fails
                           | SOME (subgoal', r') =>
                               let val tagged_step = Step (tag, tactic, n)
                               in case trace_solve_tac ctxt backtrack get_tacs data subgoal'
                                                       (option_decr depth_limit) of
                                      (_, Left fail) => if backtrack then
                                                          try_results (n+1) r'
                                                                      ({ step = tagged_step
                                                                       , trace = fail } :: fails)
                                                        else (data, Left [{ step = tagged_step, trace = fail }])
                                    | (data, Right (trace as TraceSuccess trace')) =>
                                          (data, TraceSubgoal { subgoal = subgoal
                                                              , subtheorem = #theorem trace'
                                                              , fail_steps = fails
                                                              , step = tagged_step
                                                              , subproof = trace
                                                              } |> Right)
                               end
                       in try_results 0 (tactic subgoal) fails end
               in case try_tacs (get_tacs data subgoal_term) [] of
                      (_, Left fails) => (data, TraceFailure
                                                { goal = goal0
                                                , succeeded = rev subproofs_rev
                                                , failed = { subgoal = subgoal
                                                           , fail_steps = fails
                                                           , fail_reason = SolveTac_ProofFailed
                                                           }
                                                , remaining_goals = remaining_subgoals
                                                } |> Left)
                    | (data, Right (subproof as TraceSubgoal subproof')) =>
                          let val subtheorem = #subtheorem subproof' in
                          case my_unify_fact_tac ctxt (Goal.finish ctxt subtheorem) 1 goal
                               |> Seq.pull of
                              NONE => raise THM ("trace_solve_tac: could not apply subgoal proof",
                                                 0, [goal, subtheorem])
                            | SOME (goal', _) =>
                                  if Thm.nprems_of goal' + 1 = Thm.nprems_of goal then
                                     solve data goal' (subproof :: subproofs_rev)
                                  else raise THM ("trace_solve_tac: could not apply subgoal proof",
                                                  0, [goal, subtheorem])
                          end
               end
    in solve data0 goal0 [] end
  end
*}
(* end: tactic trace code *)

ML {*
datatype 'a Tree = Tree of 'a * 'a Tree list;

fun tree_hd (Tree (head, _)) = head
fun tree_rest (Tree (_, rest)) = rest
fun tree_map f (Tree (head,rest)) = Tree (f head, map (tree_map f) rest)
*}

(* extract relevant subproofs *)
ML {*

fun filter_trace PSuccess PSubgoal (TraceSuccess tr) =
      if not (PSuccess tr) then [] else
        [ Tree (#theorem tr,
                List.concat (map (filter_TraceSubgoal PSuccess PSubgoal) (#subproofs tr))) ]
and filter_TraceSubgoal PSuccess PSubgoal (TraceSubgoal tr) =
      if not (PSubgoal tr) then [] else filter_trace PSuccess PSubgoal (#subproof tr);

fun is_const n (Const (name, _)) = n = name
  | is_const _ _ = false;

fun unprop (Const (@{const_name Pure.prop}, _) $ t) = unprop t
  | unprop (Const (@{const_name Pure.imp}, _) $ _ $ t) = unprop t
  | unprop (Const (@{const_name Pure.all}, _) $ t) = unprop t
  | unprop (Const (@{const_name HOL.Trueprop}, _) $ t) = unprop t
  | unprop t = t;
*}

ML {*
fun extract_subproofs goal tactics is_interesting ctxt =
  trace_solve_tac ctxt true
    (fn n => K [nth tactics n |> (fn (tag, tac) => (n+1, tag, tac))]) 0
    (Goal.init goal)
  NONE
|> (fn (_, result) =>
      case result of
          Right tr => Right (filter_trace (is_interesting o unprop o Thm.prop_of o #theorem) (K true) tr)
        | Left err => Left err
   )
*}

end