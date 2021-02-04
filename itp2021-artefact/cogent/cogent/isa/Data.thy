theory Data
  imports Pure
begin

(* ideally, would be a pure ML file, but it seems to break polymorphism later *)

ML \<open>

(* list things *)

fun findIndex p =
  let fun find _ [] = NONE
        | find n (x::xs) = if p x then SOME (x, n) else find (n+1) xs
  in find 0 end

fun zipWith _ [] _ = []
  | zipWith _ _ [] = []
  | zipWith f (x::xs) (y::ys) = f x y :: zipWith f xs ys

fun enumerate xs = let
  fun enum _ [] = []
    | enum n (x::xs) = (n, x) :: enum (n+1) xs
  in enum 0 xs end

fun removedups f (x :: y :: xs) = if f x <> f y then x :: removedups f (y :: xs) else removedups f (x :: xs)
  | removedups _ xs = xs

fun nubBy _ [] = []
  | nubBy f (x::xs) = x :: filter (fn y => f x <> f y) (nubBy f xs)

(* either *)
datatype ('l, 'r) Either = Left of 'l | Right of 'r

fun mapEither fl _ (Left l) = Left (fl l)
  | mapEither _ fr (Right r) = Right (fr r)

fun mapEitherL f e = mapEither f (fn x => x) e
fun mapEitherR f e = mapEither (fn x => x) f e


(* rose trees *)

datatype 'a tree = Tree of 'a * 'a tree list;

fun tree_value (Tree (v, _)) = v
fun tree_branches (Tree (_, b)) = b

val tree_hd = tree_value
val tree_rest = tree_branches

fun tree_lookup [] (Tree v) = v
| tree_lookup (i :: is) (Tree (_, bs)) = tree_lookup is (nth bs i)

fun tree_map f (Tree (v, b)) = Tree (f v, map (tree_map f) b)

fun tree_foldl f (Tree (v, b)) init = fold (tree_foldl f) b (f init v)

fun tree_foldr f (Tree (v, b)) init = f (fold_rev (tree_foldr f) b init) v

(* NB: flattening the proof tree is unsafe in general, but this program is a small example *)
fun flatten_tree (Tree (v, b)) = v :: List.concat (map flatten_tree b);

(* leaf trees

   Trees with information only at the leaves
*)

datatype 'a leaftree = Branch of 'a leaftree list | Leaf of 'a

fun leaftree_unfold (f : 'b -> ('a, ('b list)) Either) (init : 'b) : 'a leaftree = (case f init of
  Left a => Leaf a
| Right bs => Branch (map (leaftree_unfold f) bs))

fun leaftree_map f (Branch tas) = Branch (map (fn t => leaftree_map f t) tas)
  | leaftree_map f (Leaf a)     = Leaf (f a)


datatype 'a treestep = StepDown | StepUp | Val of 'a

fun parse_treesteps' [] = ([], [])
  | parse_treesteps' (StepDown :: rest) = let
    val (children, rest) = parse_treesteps' rest
    val (siblings, rest) = parse_treesteps' rest
   in (Branch children :: siblings, rest) end
  | parse_treesteps' (StepUp :: rest) = ([], rest)
  | parse_treesteps' ((Val a) :: rest) = let
      val (siblings, rest) = parse_treesteps' rest
    in (Leaf a :: siblings, rest) end

fun parse_treesteps steps = (case parse_treesteps' steps of
    ((t :: []),[]) => SOME t
  | (_,_) => NONE)

(* option things *)

fun isSome (SOME _) = true
  | isSome _ = false

fun isNone NONE = true
  | isNone _ = false

val option_decr = Option.map (fn x => x - 1)

\<close>

end