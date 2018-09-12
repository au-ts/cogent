theory Data
  imports Pure
begin

(* ideally, would be a pure ML file, but it seems to break polymorphism later *)

ML {*

(* either *)
datatype ('l, 'r) Either = Left of 'l | Right of 'r

fun mapEither fl _ (Left l) = Left (fl l)
  | mapEither _ fr (Right r) = Right (fr r)

fun mapEitherL f e = mapEither f (fn x => x) e
fun mapEitherR f e = mapEither (fn x => x) f e


(* rose trees *)

datatype 'a Tree = Tree of 'a * 'a Tree list;

fun tree_hd (Tree (head, _)) = head
fun tree_rest (Tree (_, rest)) = rest
fun tree_map f (Tree (head,rest)) = Tree (f head, map (tree_map f) rest)


(* leaf trees

   Trees with information only at the leaves
*)

datatype 'a leaftree = Branch of 'a leaftree list | Leaf of 'a

fun leaftree_map (f : 'a -> 'b) (Branch tas) = Branch (map (leaftree_map f) tas)
  | leaftree_map (f : 'a -> 'b) (Leaf a)     = Leaf (f a)

fun unfold_leaftree (f : 'b -> ('a, ('b list)) Either) (init : 'b) : 'a leaftree = (case f init of
  Left a => Leaf a
| Right bs => Branch (map (unfold_leaftree f) bs))


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

fun nubBy _ [] = []
  | nubBy f (x::xs) = x :: filter (fn y => f x <> f y) (nubBy f xs)

(* option things *)

fun isSome (SOME _) = true
  | isSome _ = false

fun isNone NONE = true
  | isNone _ = false

val option_decr = Option.map (fn x => x - 1)

*}

end