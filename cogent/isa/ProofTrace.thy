(*
 * Copyright 2016, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(NICTA_GPL)
 *)

theory ProofTrace imports Main begin

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

datatype ('l, 'r) Either = Left of 'l | Right of 'r
fun mapEither fl _ (Left l) = Left (fl l)
  | mapEither _ fr (Right r) = Right (fr r)
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
                          case resolve_tac ctxt [(Goal.finish ctxt subtheorem)] 1 goal
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

(* extract relevant subproofs *)
ML {*
datatype 'a Tree = Tree of 'a * 'a Tree list;

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


ML{*
    fun tree_hd (Tree (head, _)) = head
    fun tree_rest (Tree (_, rest)) = rest
    fun tree_map f (Tree (head,rest)) = Tree (f head, map (tree_map f) rest) 
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