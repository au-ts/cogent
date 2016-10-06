--
-- Copyright 2016, NICTA
--
-- This software may be distributed and modified according to the terms of
-- the GNU General Public License version 2. Note that NO WARRANTY is provided.
-- See "LICENSE_GPLv2.txt" for details.
--
-- @TAG(NICTA_GPL)
--

{-# LANGUAGE QuasiQuotes #-}
module Isabelle.TestTH where

import Text.PrettyPrint.ANSI.Leijen
import Isabelle.InnerAST
import Isabelle.OuterAST
import Isabelle.ExprTH

val :: Theory Type Term
val = let theoryName = "Test"
          defName = "deffo"
          typ = [isaType| int \<times> int \<Rightarrow> int |]
          term = [isaTerm| (\<lambda>x. x) y |]

        in [isaTheory|
         theory $theoryName
         imports Main
         begin
           type_synonym n = "nat"
           definition "(B \<or> C) \<and> D"
           definition "B \<or> (C \<and> D)"
           definition "(A \<equiv> B) \<longrightarrow> C"
           definition "A \<equiv> (B \<longrightarrow> C)"
           definition "\<exists> a b c. (A \<longrightarrow> C)"
           definition "(\<exists> a b c. A) \<longrightarrow> C"
           definition "True"
           definition "A x \<equiv> B x"
           definition "\<lambda>x. (x y)"
           definition "$term"
           definition "((\<lambda>x. x) y) \<equiv> (B (x y))"

           definition x :: "'a \<Rightarrow> 'b" where "A"
           definition $defName :: "$typ" where "A"
           definition x :: "int \<times> (int \<Rightarrow> int)" where "A"
           definition x :: "'a option \<Rightarrow> 'b" where "A"
           definition x :: "('a, ('b \<times> 'e) \<times> 'd) test \<Rightarrow> 'c" where "A"
           definition "A :: bool \<equiv> B"

           lemma lemma1[attribute1, attribute2 with args]: "A \<and> B"
             apply clarsimp
             done

           lemma "A \<longrightarrow> B"
             apply (clarsimp simp: blah foo bar dest: baz, clarsimp, (clarsimp | clarsimp))?
             sorry

         end
       |]

main :: IO ()
main = putDoc . pretty $ val
