(*
 * Copyright 2016, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(NICTA_GPL)
 *)

theory CogentMonad
imports Main
begin

text {*

  A non-deterministic monad. The result is a set of values "results" and a
  failure flag "mayFail". (Note: this is not the same as the non-determistic
  state monad in l4.verified. It does not model state.)

  Each element in the set is a potential result of the
  computation. The "mayFail" flag is @{const True} if there is an execution path
  in the computation that may have failed. Conversely, if "mayFail" is
  @{const False}, none of the computations resulting in the returned
  set can have failed.

*}

type_synonym 'a cogent_monad = "'a set"

text {*
  The definition of fundamental monad functions @{text return} and
  @{text bind}. The monad function @{text "return x"} does not change
  the  state, does not fail, and returns @{text "x"}.
*}

definition
  return :: "'a \<Rightarrow> 'a cogent_monad" where
  "return a \<equiv>  {a}"

text {*
  The monad function @{text "bind f g"}, also written @{text "f >>= g"},
  is the execution of @{term f} followed by the execution of @{text g}.
  The function @{text g} takes the result value \emph{and} the result
  state of @{text f} as parameter. The definition says that the result of
  the combined operation is the union of the set of sets that is created
  by @{text g} applied to the result sets of @{text f}. The combined
  operation may have failed, if @{text f} may have failed or @{text g} may
  have failed on any of the results of @{text f}.
*}

definition
  bind :: "'a cogent_monad \<Rightarrow> ('a \<Rightarrow> 'b cogent_monad) \<Rightarrow> 'b cogent_monad" (infixl ">>=" 60) where
  "m >>= f \<equiv> \<Union> (f ` m)"

subsection "Monad laws"

lemma "return a >>= f = f a"
  by (auto simp: return_def bind_def)

lemma "m >>= return = m"
  by (auto simp: return_def bind_def)

lemma "(m >>= f) >>= g = m >>= (\<lambda>x. f x >>= g)"
  by (auto simp: bind_def)

subsection "Nondeterminism"

text {*
  Basic nondeterministic functions. @{text "select A"} chooses an element
  of the set @{text A}, does not change the state, and does not fail
  (even if the set is empty). *}

definition
  select :: "'a set \<Rightarrow> 'a cogent_monad" where
  "select A \<equiv> A"

text {*  @{text "f OR g"} executes @{text f} or
  executes @{text g}. It retuns the union of results of @{text f} and
  @{text g}, and may have failed if either may have failed.
*}
definition
  alternative :: "'a cogent_monad \<Rightarrow> 'a cogent_monad \<Rightarrow> 'a cogent_monad"
where
  "alternative m n \<equiv>  m \<union> n"

lemmas monadic_simps = return_def alternative_def select_def bind_def

notation (xsymbols)  alternative (infixl "\<sqinter>" 20)

text {* We use @{text K_bind} to syntactically indicate the
  case where the return argument of the left side of a @{term bind}
  is ignored *}
definition
  K_bind [iff]: "K_bind \<equiv> \<lambda>x y. x"

nonterminal
  dobinds and dobind and nobind



syntax
  "_dobind"    :: "[pttrn, 'a] => dobind"             ("(_ <-/ _)" 10)
  ""           :: "dobind => dobinds"                 ("_")
  "_nobind"    :: "'a => dobind"                      ("_")
  "_dobinds"   :: "[dobind, dobinds] => dobinds"      ("(_);//(_)")

  "_do"        :: "[dobinds, 'a] => 'a"               ("(do (_);//   (_)//od)" 100)
syntax (xsymbols)
  "_dobind"    :: "[pttrn, 'a] => dobind"             ("(_ \<leftarrow>/ _)" 10)

translations
  "_do (_dobinds b bs) e"  == "_do b (_do bs e)"
  "_do (_nobind b) e"      == "b >>= (CONST K_bind e)"
  "do x <- a; e od"        == "a >>= (\<lambda>x. e)"

value "do x \<leftarrow> do x \<leftarrow> { (1::nat),2,3 };
                 return (x+1) 
       od ;
         return (66 :: nat)
       od"

end