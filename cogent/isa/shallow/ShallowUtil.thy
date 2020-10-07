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

theory ShallowUtil
  imports
    "HOL-Word.Word"
    "Cogent.Util"
begin

fun array_map2 :: "('a \<Rightarrow> 'b \<Rightarrow> 'a \<times> 'b) \<Rightarrow> 'a list \<Rightarrow> 'b list \<Rightarrow> ('a list \<times> 'b list)"
  where
  "array_map2 f [] [] = ([], [])"
| "array_map2 f (t # q) (t' # q') = (let (a,b) = f t t' in
                                     let (la, lb) = array_map2 f q q' in
                                     (a # la, b # lb))"

definition nth' :: "nat \<Rightarrow> 'a list \<Rightarrow> 'a"
  where "nth' n l = l ! n"

definition
  fun_app :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a \<Rightarrow> 'b" (infixr "$" 10)
where
  "f $ v \<equiv> f v"

declare fun_app_def [simp]

definition
  Let\<^sub>d\<^sub>s :: "'a \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> 'b"
where
 "Let\<^sub>d\<^sub>s s f \<equiv> f s"

definition
  take\<^sub>c\<^sub>o\<^sub>g\<^sub>e\<^sub>n\<^sub>t :: "'a \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> ('b \<times> 'a)"
where
 "take\<^sub>c\<^sub>o\<^sub>g\<^sub>e\<^sub>n\<^sub>t rec field  \<equiv> (field rec, rec)"

(* for n in range(2, 15+1):
     for k in range(1, n+1):
       print('definition "P{n}_p{k}\\<^sub>f \\<equiv> \\<lambda>({tup}). p{k}"'
             .format(n=n, k=k, tup=', '.join('p' + str(k) for k in range(1, n+1))))
     print('') *)
definition "P2_p1\<^sub>f \<equiv> \<lambda>(p1, p2). p1"
definition "P2_p2\<^sub>f \<equiv> \<lambda>(p1, p2). p2"

definition "P3_p1\<^sub>f \<equiv> \<lambda>(p1, p2, p3). p1"
definition "P3_p2\<^sub>f \<equiv> \<lambda>(p1, p2, p3). p2"
definition "P3_p3\<^sub>f \<equiv> \<lambda>(p1, p2, p3). p3"

definition "P4_p1\<^sub>f \<equiv> \<lambda>(p1, p2, p3, p4). p1"
definition "P4_p2\<^sub>f \<equiv> \<lambda>(p1, p2, p3, p4). p2"
definition "P4_p3\<^sub>f \<equiv> \<lambda>(p1, p2, p3, p4). p3"
definition "P4_p4\<^sub>f \<equiv> \<lambda>(p1, p2, p3, p4). p4"

definition "P5_p1\<^sub>f \<equiv> \<lambda>(p1, p2, p3, p4, p5). p1"
definition "P5_p2\<^sub>f \<equiv> \<lambda>(p1, p2, p3, p4, p5). p2"
definition "P5_p3\<^sub>f \<equiv> \<lambda>(p1, p2, p3, p4, p5). p3"
definition "P5_p4\<^sub>f \<equiv> \<lambda>(p1, p2, p3, p4, p5). p4"
definition "P5_p5\<^sub>f \<equiv> \<lambda>(p1, p2, p3, p4, p5). p5"

definition "P6_p1\<^sub>f \<equiv> \<lambda>(p1, p2, p3, p4, p5, p6). p1"
definition "P6_p2\<^sub>f \<equiv> \<lambda>(p1, p2, p3, p4, p5, p6). p2"
definition "P6_p3\<^sub>f \<equiv> \<lambda>(p1, p2, p3, p4, p5, p6). p3"
definition "P6_p4\<^sub>f \<equiv> \<lambda>(p1, p2, p3, p4, p5, p6). p4"
definition "P6_p5\<^sub>f \<equiv> \<lambda>(p1, p2, p3, p4, p5, p6). p5"
definition "P6_p6\<^sub>f \<equiv> \<lambda>(p1, p2, p3, p4, p5, p6). p6"

definition "P7_p1\<^sub>f \<equiv> \<lambda>(p1, p2, p3, p4, p5, p6, p7). p1"
definition "P7_p2\<^sub>f \<equiv> \<lambda>(p1, p2, p3, p4, p5, p6, p7). p2"
definition "P7_p3\<^sub>f \<equiv> \<lambda>(p1, p2, p3, p4, p5, p6, p7). p3"
definition "P7_p4\<^sub>f \<equiv> \<lambda>(p1, p2, p3, p4, p5, p6, p7). p4"
definition "P7_p5\<^sub>f \<equiv> \<lambda>(p1, p2, p3, p4, p5, p6, p7). p5"
definition "P7_p6\<^sub>f \<equiv> \<lambda>(p1, p2, p3, p4, p5, p6, p7). p6"
definition "P7_p7\<^sub>f \<equiv> \<lambda>(p1, p2, p3, p4, p5, p6, p7). p7"

definition "P8_p1\<^sub>f \<equiv> \<lambda>(p1, p2, p3, p4, p5, p6, p7, p8). p1"
definition "P8_p2\<^sub>f \<equiv> \<lambda>(p1, p2, p3, p4, p5, p6, p7, p8). p2"
definition "P8_p3\<^sub>f \<equiv> \<lambda>(p1, p2, p3, p4, p5, p6, p7, p8). p3"
definition "P8_p4\<^sub>f \<equiv> \<lambda>(p1, p2, p3, p4, p5, p6, p7, p8). p4"
definition "P8_p5\<^sub>f \<equiv> \<lambda>(p1, p2, p3, p4, p5, p6, p7, p8). p5"
definition "P8_p6\<^sub>f \<equiv> \<lambda>(p1, p2, p3, p4, p5, p6, p7, p8). p6"
definition "P8_p7\<^sub>f \<equiv> \<lambda>(p1, p2, p3, p4, p5, p6, p7, p8). p7"
definition "P8_p8\<^sub>f \<equiv> \<lambda>(p1, p2, p3, p4, p5, p6, p7, p8). p8"

definition "P9_p1\<^sub>f \<equiv> \<lambda>(p1, p2, p3, p4, p5, p6, p7, p8, p9). p1"
definition "P9_p2\<^sub>f \<equiv> \<lambda>(p1, p2, p3, p4, p5, p6, p7, p8, p9). p2"
definition "P9_p3\<^sub>f \<equiv> \<lambda>(p1, p2, p3, p4, p5, p6, p7, p8, p9). p3"
definition "P9_p4\<^sub>f \<equiv> \<lambda>(p1, p2, p3, p4, p5, p6, p7, p8, p9). p4"
definition "P9_p5\<^sub>f \<equiv> \<lambda>(p1, p2, p3, p4, p5, p6, p7, p8, p9). p5"
definition "P9_p6\<^sub>f \<equiv> \<lambda>(p1, p2, p3, p4, p5, p6, p7, p8, p9). p6"
definition "P9_p7\<^sub>f \<equiv> \<lambda>(p1, p2, p3, p4, p5, p6, p7, p8, p9). p7"
definition "P9_p8\<^sub>f \<equiv> \<lambda>(p1, p2, p3, p4, p5, p6, p7, p8, p9). p8"
definition "P9_p9\<^sub>f \<equiv> \<lambda>(p1, p2, p3, p4, p5, p6, p7, p8, p9). p9"

definition "P10_p1\<^sub>f \<equiv> \<lambda>(p1, p2, p3, p4, p5, p6, p7, p8, p9, p10). p1"
definition "P10_p2\<^sub>f \<equiv> \<lambda>(p1, p2, p3, p4, p5, p6, p7, p8, p9, p10). p2"
definition "P10_p3\<^sub>f \<equiv> \<lambda>(p1, p2, p3, p4, p5, p6, p7, p8, p9, p10). p3"
definition "P10_p4\<^sub>f \<equiv> \<lambda>(p1, p2, p3, p4, p5, p6, p7, p8, p9, p10). p4"
definition "P10_p5\<^sub>f \<equiv> \<lambda>(p1, p2, p3, p4, p5, p6, p7, p8, p9, p10). p5"
definition "P10_p6\<^sub>f \<equiv> \<lambda>(p1, p2, p3, p4, p5, p6, p7, p8, p9, p10). p6"
definition "P10_p7\<^sub>f \<equiv> \<lambda>(p1, p2, p3, p4, p5, p6, p7, p8, p9, p10). p7"
definition "P10_p8\<^sub>f \<equiv> \<lambda>(p1, p2, p3, p4, p5, p6, p7, p8, p9, p10). p8"
definition "P10_p9\<^sub>f \<equiv> \<lambda>(p1, p2, p3, p4, p5, p6, p7, p8, p9, p10). p9"
definition "P10_p10\<^sub>f \<equiv> \<lambda>(p1, p2, p3, p4, p5, p6, p7, p8, p9, p10). p10"

definition "P11_p1\<^sub>f \<equiv> \<lambda>(p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11). p1"
definition "P11_p2\<^sub>f \<equiv> \<lambda>(p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11). p2"
definition "P11_p3\<^sub>f \<equiv> \<lambda>(p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11). p3"
definition "P11_p4\<^sub>f \<equiv> \<lambda>(p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11). p4"
definition "P11_p5\<^sub>f \<equiv> \<lambda>(p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11). p5"
definition "P11_p6\<^sub>f \<equiv> \<lambda>(p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11). p6"
definition "P11_p7\<^sub>f \<equiv> \<lambda>(p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11). p7"
definition "P11_p8\<^sub>f \<equiv> \<lambda>(p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11). p8"
definition "P11_p9\<^sub>f \<equiv> \<lambda>(p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11). p9"
definition "P11_p10\<^sub>f \<equiv> \<lambda>(p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11). p10"
definition "P11_p11\<^sub>f \<equiv> \<lambda>(p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11). p11"

definition "P12_p1\<^sub>f \<equiv> \<lambda>(p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12). p1"
definition "P12_p2\<^sub>f \<equiv> \<lambda>(p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12). p2"
definition "P12_p3\<^sub>f \<equiv> \<lambda>(p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12). p3"
definition "P12_p4\<^sub>f \<equiv> \<lambda>(p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12). p4"
definition "P12_p5\<^sub>f \<equiv> \<lambda>(p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12). p5"
definition "P12_p6\<^sub>f \<equiv> \<lambda>(p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12). p6"
definition "P12_p7\<^sub>f \<equiv> \<lambda>(p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12). p7"
definition "P12_p8\<^sub>f \<equiv> \<lambda>(p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12). p8"
definition "P12_p9\<^sub>f \<equiv> \<lambda>(p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12). p9"
definition "P12_p10\<^sub>f \<equiv> \<lambda>(p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12). p10"
definition "P12_p11\<^sub>f \<equiv> \<lambda>(p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12). p11"
definition "P12_p12\<^sub>f \<equiv> \<lambda>(p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12). p12"

definition "P13_p1\<^sub>f \<equiv> \<lambda>(p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13). p1"
definition "P13_p2\<^sub>f \<equiv> \<lambda>(p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13). p2"
definition "P13_p3\<^sub>f \<equiv> \<lambda>(p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13). p3"
definition "P13_p4\<^sub>f \<equiv> \<lambda>(p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13). p4"
definition "P13_p5\<^sub>f \<equiv> \<lambda>(p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13). p5"
definition "P13_p6\<^sub>f \<equiv> \<lambda>(p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13). p6"
definition "P13_p7\<^sub>f \<equiv> \<lambda>(p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13). p7"
definition "P13_p8\<^sub>f \<equiv> \<lambda>(p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13). p8"
definition "P13_p9\<^sub>f \<equiv> \<lambda>(p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13). p9"
definition "P13_p10\<^sub>f \<equiv> \<lambda>(p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13). p10"
definition "P13_p11\<^sub>f \<equiv> \<lambda>(p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13). p11"
definition "P13_p12\<^sub>f \<equiv> \<lambda>(p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13). p12"
definition "P13_p13\<^sub>f \<equiv> \<lambda>(p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13). p13"

definition "P14_p1\<^sub>f \<equiv> \<lambda>(p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13, p14). p1"
definition "P14_p2\<^sub>f \<equiv> \<lambda>(p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13, p14). p2"
definition "P14_p3\<^sub>f \<equiv> \<lambda>(p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13, p14). p3"
definition "P14_p4\<^sub>f \<equiv> \<lambda>(p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13, p14). p4"
definition "P14_p5\<^sub>f \<equiv> \<lambda>(p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13, p14). p5"
definition "P14_p6\<^sub>f \<equiv> \<lambda>(p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13, p14). p6"
definition "P14_p7\<^sub>f \<equiv> \<lambda>(p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13, p14). p7"
definition "P14_p8\<^sub>f \<equiv> \<lambda>(p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13, p14). p8"
definition "P14_p9\<^sub>f \<equiv> \<lambda>(p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13, p14). p9"
definition "P14_p10\<^sub>f \<equiv> \<lambda>(p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13, p14). p10"
definition "P14_p11\<^sub>f \<equiv> \<lambda>(p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13, p14). p11"
definition "P14_p12\<^sub>f \<equiv> \<lambda>(p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13, p14). p12"
definition "P14_p13\<^sub>f \<equiv> \<lambda>(p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13, p14). p13"
definition "P14_p14\<^sub>f \<equiv> \<lambda>(p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13, p14). p14"

definition "P15_p1\<^sub>f \<equiv> \<lambda>(p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13, p14, p15). p1"
definition "P15_p2\<^sub>f \<equiv> \<lambda>(p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13, p14, p15). p2"
definition "P15_p3\<^sub>f \<equiv> \<lambda>(p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13, p14, p15). p3"
definition "P15_p4\<^sub>f \<equiv> \<lambda>(p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13, p14, p15). p4"
definition "P15_p5\<^sub>f \<equiv> \<lambda>(p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13, p14, p15). p5"
definition "P15_p6\<^sub>f \<equiv> \<lambda>(p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13, p14, p15). p6"
definition "P15_p7\<^sub>f \<equiv> \<lambda>(p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13, p14, p15). p7"
definition "P15_p8\<^sub>f \<equiv> \<lambda>(p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13, p14, p15). p8"
definition "P15_p9\<^sub>f \<equiv> \<lambda>(p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13, p14, p15). p9"
definition "P15_p10\<^sub>f \<equiv> \<lambda>(p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13, p14, p15). p10"
definition "P15_p11\<^sub>f \<equiv> \<lambda>(p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13, p14, p15). p11"
definition "P15_p12\<^sub>f \<equiv> \<lambda>(p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13, p14, p15). p12"
definition "P15_p13\<^sub>f \<equiv> \<lambda>(p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13, p14, p15). p13"
definition "P15_p14\<^sub>f \<equiv> \<lambda>(p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13, p14, p15). p14"
definition "P15_p15\<^sub>f \<equiv> \<lambda>(p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13, p14, p15). p15"

(* for n in range(2, 15+1):
     print('lemmas P{}_px ='.format(n))
     for k in range(1, n+1):
       print('  P{}_p{}\\<^sub>f_def'.format(n, k))
     print('') *)
lemmas P2_px =
  P2_p1\<^sub>f_def
  P2_p2\<^sub>f_def

lemmas P3_px =
  P3_p1\<^sub>f_def
  P3_p2\<^sub>f_def
  P3_p3\<^sub>f_def

lemmas P4_px =
  P4_p1\<^sub>f_def
  P4_p2\<^sub>f_def
  P4_p3\<^sub>f_def
  P4_p4\<^sub>f_def

lemmas P5_px =
  P5_p1\<^sub>f_def
  P5_p2\<^sub>f_def
  P5_p3\<^sub>f_def
  P5_p4\<^sub>f_def
  P5_p5\<^sub>f_def

lemmas P6_px =
  P6_p1\<^sub>f_def
  P6_p2\<^sub>f_def
  P6_p3\<^sub>f_def
  P6_p4\<^sub>f_def
  P6_p5\<^sub>f_def
  P6_p6\<^sub>f_def

lemmas P7_px =
  P7_p1\<^sub>f_def
  P7_p2\<^sub>f_def
  P7_p3\<^sub>f_def
  P7_p4\<^sub>f_def
  P7_p5\<^sub>f_def
  P7_p6\<^sub>f_def
  P7_p7\<^sub>f_def

lemmas P8_px =
  P8_p1\<^sub>f_def
  P8_p2\<^sub>f_def
  P8_p3\<^sub>f_def
  P8_p4\<^sub>f_def
  P8_p5\<^sub>f_def
  P8_p6\<^sub>f_def
  P8_p7\<^sub>f_def
  P8_p8\<^sub>f_def

lemmas P9_px =
  P9_p1\<^sub>f_def
  P9_p2\<^sub>f_def
  P9_p3\<^sub>f_def
  P9_p4\<^sub>f_def
  P9_p5\<^sub>f_def
  P9_p6\<^sub>f_def
  P9_p7\<^sub>f_def
  P9_p8\<^sub>f_def
  P9_p9\<^sub>f_def

lemmas P10_px =
  P10_p1\<^sub>f_def
  P10_p2\<^sub>f_def
  P10_p3\<^sub>f_def
  P10_p4\<^sub>f_def
  P10_p5\<^sub>f_def
  P10_p6\<^sub>f_def
  P10_p7\<^sub>f_def
  P10_p8\<^sub>f_def
  P10_p9\<^sub>f_def
  P10_p10\<^sub>f_def

lemmas P11_px =
  P11_p1\<^sub>f_def
  P11_p2\<^sub>f_def
  P11_p3\<^sub>f_def
  P11_p4\<^sub>f_def
  P11_p5\<^sub>f_def
  P11_p6\<^sub>f_def
  P11_p7\<^sub>f_def
  P11_p8\<^sub>f_def
  P11_p9\<^sub>f_def
  P11_p10\<^sub>f_def
  P11_p11\<^sub>f_def

lemmas P12_px =
  P12_p1\<^sub>f_def
  P12_p2\<^sub>f_def
  P12_p3\<^sub>f_def
  P12_p4\<^sub>f_def
  P12_p5\<^sub>f_def
  P12_p6\<^sub>f_def
  P12_p7\<^sub>f_def
  P12_p8\<^sub>f_def
  P12_p9\<^sub>f_def
  P12_p10\<^sub>f_def
  P12_p11\<^sub>f_def
  P12_p12\<^sub>f_def

lemmas P13_px =
  P13_p1\<^sub>f_def
  P13_p2\<^sub>f_def
  P13_p3\<^sub>f_def
  P13_p4\<^sub>f_def
  P13_p5\<^sub>f_def
  P13_p6\<^sub>f_def
  P13_p7\<^sub>f_def
  P13_p8\<^sub>f_def
  P13_p9\<^sub>f_def
  P13_p10\<^sub>f_def
  P13_p11\<^sub>f_def
  P13_p12\<^sub>f_def
  P13_p13\<^sub>f_def

lemmas P14_px =
  P14_p1\<^sub>f_def
  P14_p2\<^sub>f_def
  P14_p3\<^sub>f_def
  P14_p4\<^sub>f_def
  P14_p5\<^sub>f_def
  P14_p6\<^sub>f_def
  P14_p7\<^sub>f_def
  P14_p8\<^sub>f_def
  P14_p9\<^sub>f_def
  P14_p10\<^sub>f_def
  P14_p11\<^sub>f_def
  P14_p12\<^sub>f_def
  P14_p13\<^sub>f_def
  P14_p14\<^sub>f_def

lemmas P15_px =
  P15_p1\<^sub>f_def
  P15_p2\<^sub>f_def
  P15_p3\<^sub>f_def
  P15_p4\<^sub>f_def
  P15_p5\<^sub>f_def
  P15_p6\<^sub>f_def
  P15_p7\<^sub>f_def
  P15_p8\<^sub>f_def
  P15_p9\<^sub>f_def
  P15_p10\<^sub>f_def
  P15_p11\<^sub>f_def
  P15_p12\<^sub>f_def
  P15_p13\<^sub>f_def
  P15_p14\<^sub>f_def
  P15_p15\<^sub>f_def

(* print('lemmas Px_px = ' + ' '.join('P{}_px'.format(n) for n in range(2, 15+1))) *)
lemmas Px_px = P2_px P3_px P4_px P5_px P6_px P7_px P8_px P9_px P10_px P11_px P12_px P13_px P14_px P15_px

(*
for n in range(2, 15+1):
  vars = ' '.join('x' + str(k) for k in range(1, n+1))
  print('  "(let ' +
        ';\n        '.join('(x{k}, r) = take\\<^sub>c\\<^sub>d\\<^sub>s\\<^sub>l {r} P{n}_p{k}\\<^sub>f'.
                           format(n=n, k=k, r='r' if k>1 else 'R'+str(n)) for k in range(1, n+1)) +
        '\n    in Q' + str(n) + ' ' + vars + ') =\n' +
        '   (let (' + ', '.join('x' + str(k) for k in range(1, n+1)) + ') = R' + str(n) + ' in Q' + str(n) + ' ' + vars + ')"')
*)
lemma tuple_simps:
  "(let (x1, r) = take\<^sub>c\<^sub>o\<^sub>g\<^sub>e\<^sub>n\<^sub>t R2 P2_p1\<^sub>f;
        (x2, r) = take\<^sub>c\<^sub>o\<^sub>g\<^sub>e\<^sub>n\<^sub>t r P2_p2\<^sub>f
    in Q2 x1 x2) =
   (let (x1, x2) = R2 in Q2 x1 x2)"
  "(let (x1, r) = take\<^sub>c\<^sub>o\<^sub>g\<^sub>e\<^sub>n\<^sub>t R3 P3_p1\<^sub>f;
        (x2, r) = take\<^sub>c\<^sub>o\<^sub>g\<^sub>e\<^sub>n\<^sub>t r P3_p2\<^sub>f;
        (x3, r) = take\<^sub>c\<^sub>o\<^sub>g\<^sub>e\<^sub>n\<^sub>t r P3_p3\<^sub>f
    in Q3 x1 x2 x3) =
   (let (x1, x2, x3) = R3 in Q3 x1 x2 x3)"
  "(let (x1, r) = take\<^sub>c\<^sub>o\<^sub>g\<^sub>e\<^sub>n\<^sub>t R4 P4_p1\<^sub>f;
        (x2, r) = take\<^sub>c\<^sub>o\<^sub>g\<^sub>e\<^sub>n\<^sub>t r P4_p2\<^sub>f;
        (x3, r) = take\<^sub>c\<^sub>o\<^sub>g\<^sub>e\<^sub>n\<^sub>t r P4_p3\<^sub>f;
        (x4, r) = take\<^sub>c\<^sub>o\<^sub>g\<^sub>e\<^sub>n\<^sub>t r P4_p4\<^sub>f
    in Q4 x1 x2 x3 x4) =
   (let (x1, x2, x3, x4) = R4 in Q4 x1 x2 x3 x4)"
  "(let (x1, r) = take\<^sub>c\<^sub>o\<^sub>g\<^sub>e\<^sub>n\<^sub>t R5 P5_p1\<^sub>f;
        (x2, r) = take\<^sub>c\<^sub>o\<^sub>g\<^sub>e\<^sub>n\<^sub>t r P5_p2\<^sub>f;
        (x3, r) = take\<^sub>c\<^sub>o\<^sub>g\<^sub>e\<^sub>n\<^sub>t r P5_p3\<^sub>f;
        (x4, r) = take\<^sub>c\<^sub>o\<^sub>g\<^sub>e\<^sub>n\<^sub>t r P5_p4\<^sub>f;
        (x5, r) = take\<^sub>c\<^sub>o\<^sub>g\<^sub>e\<^sub>n\<^sub>t r P5_p5\<^sub>f
    in Q5 x1 x2 x3 x4 x5) =
   (let (x1, x2, x3, x4, x5) = R5 in Q5 x1 x2 x3 x4 x5)"
  "(let (x1, r) = take\<^sub>c\<^sub>o\<^sub>g\<^sub>e\<^sub>n\<^sub>t R6 P6_p1\<^sub>f;
        (x2, r) = take\<^sub>c\<^sub>o\<^sub>g\<^sub>e\<^sub>n\<^sub>t r P6_p2\<^sub>f;
        (x3, r) = take\<^sub>c\<^sub>o\<^sub>g\<^sub>e\<^sub>n\<^sub>t r P6_p3\<^sub>f;
        (x4, r) = take\<^sub>c\<^sub>o\<^sub>g\<^sub>e\<^sub>n\<^sub>t r P6_p4\<^sub>f;
        (x5, r) = take\<^sub>c\<^sub>o\<^sub>g\<^sub>e\<^sub>n\<^sub>t r P6_p5\<^sub>f;
        (x6, r) = take\<^sub>c\<^sub>o\<^sub>g\<^sub>e\<^sub>n\<^sub>t r P6_p6\<^sub>f
    in Q6 x1 x2 x3 x4 x5 x6) =
   (let (x1, x2, x3, x4, x5, x6) = R6 in Q6 x1 x2 x3 x4 x5 x6)"
  "(let (x1, r) = take\<^sub>c\<^sub>o\<^sub>g\<^sub>e\<^sub>n\<^sub>t R7 P7_p1\<^sub>f;
        (x2, r) = take\<^sub>c\<^sub>o\<^sub>g\<^sub>e\<^sub>n\<^sub>t r P7_p2\<^sub>f;
        (x3, r) = take\<^sub>c\<^sub>o\<^sub>g\<^sub>e\<^sub>n\<^sub>t r P7_p3\<^sub>f;
        (x4, r) = take\<^sub>c\<^sub>o\<^sub>g\<^sub>e\<^sub>n\<^sub>t r P7_p4\<^sub>f;
        (x5, r) = take\<^sub>c\<^sub>o\<^sub>g\<^sub>e\<^sub>n\<^sub>t r P7_p5\<^sub>f;
        (x6, r) = take\<^sub>c\<^sub>o\<^sub>g\<^sub>e\<^sub>n\<^sub>t r P7_p6\<^sub>f;
        (x7, r) = take\<^sub>c\<^sub>o\<^sub>g\<^sub>e\<^sub>n\<^sub>t r P7_p7\<^sub>f
    in Q7 x1 x2 x3 x4 x5 x6 x7) =
   (let (x1, x2, x3, x4, x5, x6, x7) = R7 in Q7 x1 x2 x3 x4 x5 x6 x7)"
  "(let (x1, r) = take\<^sub>c\<^sub>o\<^sub>g\<^sub>e\<^sub>n\<^sub>t R8 P8_p1\<^sub>f;
        (x2, r) = take\<^sub>c\<^sub>o\<^sub>g\<^sub>e\<^sub>n\<^sub>t r P8_p2\<^sub>f;
        (x3, r) = take\<^sub>c\<^sub>o\<^sub>g\<^sub>e\<^sub>n\<^sub>t r P8_p3\<^sub>f;
        (x4, r) = take\<^sub>c\<^sub>o\<^sub>g\<^sub>e\<^sub>n\<^sub>t r P8_p4\<^sub>f;
        (x5, r) = take\<^sub>c\<^sub>o\<^sub>g\<^sub>e\<^sub>n\<^sub>t r P8_p5\<^sub>f;
        (x6, r) = take\<^sub>c\<^sub>o\<^sub>g\<^sub>e\<^sub>n\<^sub>t r P8_p6\<^sub>f;
        (x7, r) = take\<^sub>c\<^sub>o\<^sub>g\<^sub>e\<^sub>n\<^sub>t r P8_p7\<^sub>f;
        (x8, r) = take\<^sub>c\<^sub>o\<^sub>g\<^sub>e\<^sub>n\<^sub>t r P8_p8\<^sub>f
    in Q8 x1 x2 x3 x4 x5 x6 x7 x8) =
   (let (x1, x2, x3, x4, x5, x6, x7, x8) = R8 in Q8 x1 x2 x3 x4 x5 x6 x7 x8)"
  "(let (x1, r) = take\<^sub>c\<^sub>o\<^sub>g\<^sub>e\<^sub>n\<^sub>t R9 P9_p1\<^sub>f;
        (x2, r) = take\<^sub>c\<^sub>o\<^sub>g\<^sub>e\<^sub>n\<^sub>t r P9_p2\<^sub>f;
        (x3, r) = take\<^sub>c\<^sub>o\<^sub>g\<^sub>e\<^sub>n\<^sub>t r P9_p3\<^sub>f;
        (x4, r) = take\<^sub>c\<^sub>o\<^sub>g\<^sub>e\<^sub>n\<^sub>t r P9_p4\<^sub>f;
        (x5, r) = take\<^sub>c\<^sub>o\<^sub>g\<^sub>e\<^sub>n\<^sub>t r P9_p5\<^sub>f;
        (x6, r) = take\<^sub>c\<^sub>o\<^sub>g\<^sub>e\<^sub>n\<^sub>t r P9_p6\<^sub>f;
        (x7, r) = take\<^sub>c\<^sub>o\<^sub>g\<^sub>e\<^sub>n\<^sub>t r P9_p7\<^sub>f;
        (x8, r) = take\<^sub>c\<^sub>o\<^sub>g\<^sub>e\<^sub>n\<^sub>t r P9_p8\<^sub>f;
        (x9, r) = take\<^sub>c\<^sub>o\<^sub>g\<^sub>e\<^sub>n\<^sub>t r P9_p9\<^sub>f
    in Q9 x1 x2 x3 x4 x5 x6 x7 x8 x9) =
   (let (x1, x2, x3, x4, x5, x6, x7, x8, x9) = R9 in Q9 x1 x2 x3 x4 x5 x6 x7 x8 x9)"
  "(let (x1, r) = take\<^sub>c\<^sub>o\<^sub>g\<^sub>e\<^sub>n\<^sub>t R10 P10_p1\<^sub>f;
        (x2, r) = take\<^sub>c\<^sub>o\<^sub>g\<^sub>e\<^sub>n\<^sub>t r P10_p2\<^sub>f;
        (x3, r) = take\<^sub>c\<^sub>o\<^sub>g\<^sub>e\<^sub>n\<^sub>t r P10_p3\<^sub>f;
        (x4, r) = take\<^sub>c\<^sub>o\<^sub>g\<^sub>e\<^sub>n\<^sub>t r P10_p4\<^sub>f;
        (x5, r) = take\<^sub>c\<^sub>o\<^sub>g\<^sub>e\<^sub>n\<^sub>t r P10_p5\<^sub>f;
        (x6, r) = take\<^sub>c\<^sub>o\<^sub>g\<^sub>e\<^sub>n\<^sub>t r P10_p6\<^sub>f;
        (x7, r) = take\<^sub>c\<^sub>o\<^sub>g\<^sub>e\<^sub>n\<^sub>t r P10_p7\<^sub>f;
        (x8, r) = take\<^sub>c\<^sub>o\<^sub>g\<^sub>e\<^sub>n\<^sub>t r P10_p8\<^sub>f;
        (x9, r) = take\<^sub>c\<^sub>o\<^sub>g\<^sub>e\<^sub>n\<^sub>t r P10_p9\<^sub>f;
        (x10, r) = take\<^sub>c\<^sub>o\<^sub>g\<^sub>e\<^sub>n\<^sub>t r P10_p10\<^sub>f
    in Q10 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10) =
   (let (x1, x2, x3, x4, x5, x6, x7, x8, x9, x10) = R10 in Q10 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10)"
  "(let (x1, r) = take\<^sub>c\<^sub>o\<^sub>g\<^sub>e\<^sub>n\<^sub>t R11 P11_p1\<^sub>f;
        (x2, r) = take\<^sub>c\<^sub>o\<^sub>g\<^sub>e\<^sub>n\<^sub>t r P11_p2\<^sub>f;
        (x3, r) = take\<^sub>c\<^sub>o\<^sub>g\<^sub>e\<^sub>n\<^sub>t r P11_p3\<^sub>f;
        (x4, r) = take\<^sub>c\<^sub>o\<^sub>g\<^sub>e\<^sub>n\<^sub>t r P11_p4\<^sub>f;
        (x5, r) = take\<^sub>c\<^sub>o\<^sub>g\<^sub>e\<^sub>n\<^sub>t r P11_p5\<^sub>f;
        (x6, r) = take\<^sub>c\<^sub>o\<^sub>g\<^sub>e\<^sub>n\<^sub>t r P11_p6\<^sub>f;
        (x7, r) = take\<^sub>c\<^sub>o\<^sub>g\<^sub>e\<^sub>n\<^sub>t r P11_p7\<^sub>f;
        (x8, r) = take\<^sub>c\<^sub>o\<^sub>g\<^sub>e\<^sub>n\<^sub>t r P11_p8\<^sub>f;
        (x9, r) = take\<^sub>c\<^sub>o\<^sub>g\<^sub>e\<^sub>n\<^sub>t r P11_p9\<^sub>f;
        (x10, r) = take\<^sub>c\<^sub>o\<^sub>g\<^sub>e\<^sub>n\<^sub>t r P11_p10\<^sub>f;
        (x11, r) = take\<^sub>c\<^sub>o\<^sub>g\<^sub>e\<^sub>n\<^sub>t r P11_p11\<^sub>f
    in Q11 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11) =
   (let (x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11) = R11 in Q11 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11)"
  "(let (x1, r) = take\<^sub>c\<^sub>o\<^sub>g\<^sub>e\<^sub>n\<^sub>t R12 P12_p1\<^sub>f;
        (x2, r) = take\<^sub>c\<^sub>o\<^sub>g\<^sub>e\<^sub>n\<^sub>t r P12_p2\<^sub>f;
        (x3, r) = take\<^sub>c\<^sub>o\<^sub>g\<^sub>e\<^sub>n\<^sub>t r P12_p3\<^sub>f;
        (x4, r) = take\<^sub>c\<^sub>o\<^sub>g\<^sub>e\<^sub>n\<^sub>t r P12_p4\<^sub>f;
        (x5, r) = take\<^sub>c\<^sub>o\<^sub>g\<^sub>e\<^sub>n\<^sub>t r P12_p5\<^sub>f;
        (x6, r) = take\<^sub>c\<^sub>o\<^sub>g\<^sub>e\<^sub>n\<^sub>t r P12_p6\<^sub>f;
        (x7, r) = take\<^sub>c\<^sub>o\<^sub>g\<^sub>e\<^sub>n\<^sub>t r P12_p7\<^sub>f;
        (x8, r) = take\<^sub>c\<^sub>o\<^sub>g\<^sub>e\<^sub>n\<^sub>t r P12_p8\<^sub>f;
        (x9, r) = take\<^sub>c\<^sub>o\<^sub>g\<^sub>e\<^sub>n\<^sub>t r P12_p9\<^sub>f;
        (x10, r) = take\<^sub>c\<^sub>o\<^sub>g\<^sub>e\<^sub>n\<^sub>t r P12_p10\<^sub>f;
        (x11, r) = take\<^sub>c\<^sub>o\<^sub>g\<^sub>e\<^sub>n\<^sub>t r P12_p11\<^sub>f;
        (x12, r) = take\<^sub>c\<^sub>o\<^sub>g\<^sub>e\<^sub>n\<^sub>t r P12_p12\<^sub>f
    in Q12 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12) =
   (let (x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12) = R12 in Q12 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12)"
  "(let (x1, r) = take\<^sub>c\<^sub>o\<^sub>g\<^sub>e\<^sub>n\<^sub>t R13 P13_p1\<^sub>f;
        (x2, r) = take\<^sub>c\<^sub>o\<^sub>g\<^sub>e\<^sub>n\<^sub>t r P13_p2\<^sub>f;
        (x3, r) = take\<^sub>c\<^sub>o\<^sub>g\<^sub>e\<^sub>n\<^sub>t r P13_p3\<^sub>f;
        (x4, r) = take\<^sub>c\<^sub>o\<^sub>g\<^sub>e\<^sub>n\<^sub>t r P13_p4\<^sub>f;
        (x5, r) = take\<^sub>c\<^sub>o\<^sub>g\<^sub>e\<^sub>n\<^sub>t r P13_p5\<^sub>f;
        (x6, r) = take\<^sub>c\<^sub>o\<^sub>g\<^sub>e\<^sub>n\<^sub>t r P13_p6\<^sub>f;
        (x7, r) = take\<^sub>c\<^sub>o\<^sub>g\<^sub>e\<^sub>n\<^sub>t r P13_p7\<^sub>f;
        (x8, r) = take\<^sub>c\<^sub>o\<^sub>g\<^sub>e\<^sub>n\<^sub>t r P13_p8\<^sub>f;
        (x9, r) = take\<^sub>c\<^sub>o\<^sub>g\<^sub>e\<^sub>n\<^sub>t r P13_p9\<^sub>f;
        (x10, r) = take\<^sub>c\<^sub>o\<^sub>g\<^sub>e\<^sub>n\<^sub>t r P13_p10\<^sub>f;
        (x11, r) = take\<^sub>c\<^sub>o\<^sub>g\<^sub>e\<^sub>n\<^sub>t r P13_p11\<^sub>f;
        (x12, r) = take\<^sub>c\<^sub>o\<^sub>g\<^sub>e\<^sub>n\<^sub>t r P13_p12\<^sub>f;
        (x13, r) = take\<^sub>c\<^sub>o\<^sub>g\<^sub>e\<^sub>n\<^sub>t r P13_p13\<^sub>f
    in Q13 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13) =
   (let (x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13) = R13 in Q13 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13)"
  "(let (x1, r) = take\<^sub>c\<^sub>o\<^sub>g\<^sub>e\<^sub>n\<^sub>t R14 P14_p1\<^sub>f;
        (x2, r) = take\<^sub>c\<^sub>o\<^sub>g\<^sub>e\<^sub>n\<^sub>t r P14_p2\<^sub>f;
        (x3, r) = take\<^sub>c\<^sub>o\<^sub>g\<^sub>e\<^sub>n\<^sub>t r P14_p3\<^sub>f;
        (x4, r) = take\<^sub>c\<^sub>o\<^sub>g\<^sub>e\<^sub>n\<^sub>t r P14_p4\<^sub>f;
        (x5, r) = take\<^sub>c\<^sub>o\<^sub>g\<^sub>e\<^sub>n\<^sub>t r P14_p5\<^sub>f;
        (x6, r) = take\<^sub>c\<^sub>o\<^sub>g\<^sub>e\<^sub>n\<^sub>t r P14_p6\<^sub>f;
        (x7, r) = take\<^sub>c\<^sub>o\<^sub>g\<^sub>e\<^sub>n\<^sub>t r P14_p7\<^sub>f;
        (x8, r) = take\<^sub>c\<^sub>o\<^sub>g\<^sub>e\<^sub>n\<^sub>t r P14_p8\<^sub>f;
        (x9, r) = take\<^sub>c\<^sub>o\<^sub>g\<^sub>e\<^sub>n\<^sub>t r P14_p9\<^sub>f;
        (x10, r) = take\<^sub>c\<^sub>o\<^sub>g\<^sub>e\<^sub>n\<^sub>t r P14_p10\<^sub>f;
        (x11, r) = take\<^sub>c\<^sub>o\<^sub>g\<^sub>e\<^sub>n\<^sub>t r P14_p11\<^sub>f;
        (x12, r) = take\<^sub>c\<^sub>o\<^sub>g\<^sub>e\<^sub>n\<^sub>t r P14_p12\<^sub>f;
        (x13, r) = take\<^sub>c\<^sub>o\<^sub>g\<^sub>e\<^sub>n\<^sub>t r P14_p13\<^sub>f;
        (x14, r) = take\<^sub>c\<^sub>o\<^sub>g\<^sub>e\<^sub>n\<^sub>t r P14_p14\<^sub>f
    in Q14 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14) =
   (let (x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14) = R14 in Q14 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14)"
  "(let (x1, r) = take\<^sub>c\<^sub>o\<^sub>g\<^sub>e\<^sub>n\<^sub>t R15 P15_p1\<^sub>f;
        (x2, r) = take\<^sub>c\<^sub>o\<^sub>g\<^sub>e\<^sub>n\<^sub>t r P15_p2\<^sub>f;
        (x3, r) = take\<^sub>c\<^sub>o\<^sub>g\<^sub>e\<^sub>n\<^sub>t r P15_p3\<^sub>f;
        (x4, r) = take\<^sub>c\<^sub>o\<^sub>g\<^sub>e\<^sub>n\<^sub>t r P15_p4\<^sub>f;
        (x5, r) = take\<^sub>c\<^sub>o\<^sub>g\<^sub>e\<^sub>n\<^sub>t r P15_p5\<^sub>f;
        (x6, r) = take\<^sub>c\<^sub>o\<^sub>g\<^sub>e\<^sub>n\<^sub>t r P15_p6\<^sub>f;
        (x7, r) = take\<^sub>c\<^sub>o\<^sub>g\<^sub>e\<^sub>n\<^sub>t r P15_p7\<^sub>f;
        (x8, r) = take\<^sub>c\<^sub>o\<^sub>g\<^sub>e\<^sub>n\<^sub>t r P15_p8\<^sub>f;
        (x9, r) = take\<^sub>c\<^sub>o\<^sub>g\<^sub>e\<^sub>n\<^sub>t r P15_p9\<^sub>f;
        (x10, r) = take\<^sub>c\<^sub>o\<^sub>g\<^sub>e\<^sub>n\<^sub>t r P15_p10\<^sub>f;
        (x11, r) = take\<^sub>c\<^sub>o\<^sub>g\<^sub>e\<^sub>n\<^sub>t r P15_p11\<^sub>f;
        (x12, r) = take\<^sub>c\<^sub>o\<^sub>g\<^sub>e\<^sub>n\<^sub>t r P15_p12\<^sub>f;
        (x13, r) = take\<^sub>c\<^sub>o\<^sub>g\<^sub>e\<^sub>n\<^sub>t r P15_p13\<^sub>f;
        (x14, r) = take\<^sub>c\<^sub>o\<^sub>g\<^sub>e\<^sub>n\<^sub>t r P15_p14\<^sub>f;
        (x15, r) = take\<^sub>c\<^sub>o\<^sub>g\<^sub>e\<^sub>n\<^sub>t r P15_p15\<^sub>f
    in Q15 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15) =
   (let (x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15) = R15 in Q15 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15)"
  by (simp add: Let_def prod.case_eq_if take\<^sub>c\<^sub>o\<^sub>g\<^sub>e\<^sub>n\<^sub>t_def Px_px)+

end