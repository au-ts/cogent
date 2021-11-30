(*
 * Copyright 2016, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(NICTA_GPL)
 *)

theory ArrayT

imports "../lib/TypBucket"
        "../adt/BilbyT"
        "../adt/WordArrayT"
        "../lib/Loops"

begin


consts \<alpha>a :: "'a Array \<Rightarrow> 'a Option\<^sub>T list"
consts make :: "'a Option\<^sub>T list \<Rightarrow> 'a Array"
(* I believe we could simplify this by converting the 'a Option\<^sub>T list to a
 'a list first using trimNone  *)
fun trimNone :: "'a Option\<^sub>T list \<Rightarrow> 'a list"
where
  "trimNone [] = []" |
  "trimNone (Option.None ()#xs) = trimNone xs" |
  "trimNone (Option.Some v#xs) = v#(trimNone xs)"

definition
 map_acc_obs_existing :: "('a \<times> 'acc \<times> 'obsv \<Rightarrow> ('a \<times> 'b, 'a \<times> 'acc) LoopResult)
   \<Rightarrow> 'a Option\<^sub>T list
    \<Rightarrow> 'acc \<Rightarrow> 'obsv \<Rightarrow> 'a Option\<^sub>T list \<times>
                     ('b, 'acc) LoopResult"
where
  "map_acc_obs_existing fx xs xacc obs =
     fold (\<lambda>val (ys,lr).
      (case val of Option.None _ \<Rightarrow>
        (ys@[Option.None ()], lr)
       | Option.Some tval \<Rightarrow>
       (case lr of Break xrbrk \<Rightarrow> (ys@[Option.Some tval],Break xrbrk)
         | Iterate accx \<Rightarrow> 
          (case fx (tval,accx,obs) of  \<comment> \<open>This is wrong break returns a truncated array\<close>
           Break (tval,xrbrk) \<Rightarrow> (ys@[Option.Some tval], Break xrbrk)
           | Iterate (tval,accx) \<Rightarrow> (ys@[Option.Some tval], Iterate accx)))))
       xs ([],Iterate xacc)"

definition 
 arr_iterate_ex_no_break_body :: "(('a, 'acc, 'obsv) ElemAO \<Rightarrow> ('acc \<times> (unit, 'a) R\<^sub>T))
   \<Rightarrow> 'a Option\<^sub>T \<Rightarrow> 'a Option\<^sub>T list \<times> 'acc \<Rightarrow> 'obsv \<Rightarrow> 'a Option\<^sub>T list \<times> 'acc" where
 "arr_iterate_ex_no_break_body \<equiv> \<lambda> body el (ys, acc) obs.
     case el of
        Option.None _ \<Rightarrow> (ys@[Option.None ()], acc)
      | Option.Some tval \<Rightarrow>
        (let (acc, r) = body (ElemAO.make  tval acc obs)
          in case r of
               Result.Success _ \<Rightarrow> (ys @ [ Option.None () :: 'a Option\<^sub>T], acc)
             | Result.Error   a \<Rightarrow> (ys @ [ Option.Some a ], acc))"

definition
 "array_iterate_ex_no_break body xs accx obs \<equiv>
   arr_iteratei (length xs) xs (\<lambda>_. True) (arr_iterate_ex_no_break_body body) ([],accx) obs"


definition
  mapAccumObsOpt :: "nat \<Rightarrow> nat \<Rightarrow> 
    (('a Option\<^sub>T, 'acc, 'obsv) OptElemAO
      \<Rightarrow> ('a Option\<^sub>T \<times> 'd, 'a Option\<^sub>T \<times> 'acc) LoopResult)
   \<Rightarrow> 'a Option\<^sub>T list \<Rightarrow> 'acc \<Rightarrow> 'obsv \<Rightarrow> ('a Option\<^sub>T list \<times> 'd, 'a Option\<^sub>T list \<times> 'acc) LoopResult"
where
  "mapAccumObsOpt frm to fn xs vacc obs =
   (case (fold (\<lambda>elem iter.
                (case iter 
                  of Iterate (ys, acc)  \<Rightarrow>
                     (case fn (OptElemAO.make elem acc obs) 
                       of Iterate (oelem, acc) \<Rightarrow> Iterate (ys @ [oelem], acc)
                        | Break (oelem, d) \<Rightarrow> Break (ys @ [oelem], d))
                   | Break (ys, d) \<Rightarrow> Break (ys @ [elem], d)))
               (slice frm to xs) (Iterate ([],vacc)))
     of Iterate (ys, acc) \<Rightarrow> Iterate (take frm xs @ ys @ drop (max frm to) xs, acc) 
      | Break  (ys, d) \<Rightarrow> Break (take frm xs @ ys @ drop (max frm to) xs, d))"

axiomatization where 
  array_make: "\<alpha>a (ArrayT.make xs) = xs"
  and
  array_make': "ArrayT.make (\<alpha>a a) = a"
  and
  array_create_ret:
   "\<lbrakk>  \<And>ex'. (ex',Option.None ()) = malloc ex \<Longrightarrow> P (Error ex');
       \<And>ex' arr a. \<lbrakk> sz > 0 ; (ex', Option.Some arr) = malloc ex; 
             \<alpha>a a = replicate (unat sz) (Option.None ()) \<rbrakk> \<Longrightarrow>
           P (Success (ex', a))
     \<rbrakk> \<Longrightarrow>
      P (array_create (ex, sz))"
  and 
  array_length_ret:
   "unat (array_length arr) = length (\<alpha>a arr)"
  and
  array_nb_elem_ret:
   "unat (array_nb_elem arrx) = \<alpha>_array_nb_elem (\<alpha>a arrx)"
  and
  array_modify_ret:
   "\<And>P r arr'. \<lbrakk> unat index < length (\<alpha>a arr);
       r = modifier (OptElemA.make ((\<alpha>a arr)!unat index)  acc);
       arr' = ArrayT.make ((\<alpha>a arr)[unat index:= OptElemA.oelem\<^sub>f r]);
       P (\<lparr> ArrA.arr\<^sub>f = arr', acc\<^sub>f = (OptElemA.acc\<^sub>f r) \<rparr>) \<rbrakk> \<Longrightarrow>
        P (array_modify (ArrayModifyP.make arr index modifier acc))"
      (* arr' = snd (select (arr,{v. \<alpha>a v = (\<alpha>a arr)[unat index:=Some (OptElemA.oelem\<^sub>f r)]})); *)
(*
axiomatization where array_iterate_existing_ret:
   "\<And>P. P (map_acc_obs_existing body (\<alpha>a arrx) accx obs) 
   \<Longrightarrow> case array_iterate_existing (arrx, body, accx, obs) of
        Break (arrx,rbrkx) \<Rightarrow> P ((\<alpha>a arrx), Break rbrkx)
       | Iterate (arrx, accx) \<Rightarrow> P ((\<alpha>a arrx), Iterate accx)"
*)
  and 
  array_iterate_enb_ret:
   "\<And>P. let (arr, acc) = array_iterate_ex_no_break body (\<alpha>a arr) acc obs
        in P (ArrA.make (ArrayT.make arr) acc)
   \<Longrightarrow> P (array_filter (ArrayFoldP.make arr body acc obs))"
 and array_map_ret:
  "array_map am = 
   (case (mapAccumObsOpt 
      (unat (ArrayMapP.frm\<^sub>f am)) (unat (ArrayMapP.to\<^sub>f am)) (ArrayMapP.f\<^sub>f am) 
      (\<alpha>a (ArrayMapP.arr\<^sub>f am)) (ArrayMapP.acc\<^sub>f am) (ArrayMapP.obsv\<^sub>f am)) 
    of Iterate (ys, acc) \<Rightarrow>  Iterate (ArrayT.make ys, acc)
     | Break  (ys, d) \<Rightarrow> Break(ArrayT.make ys, d))" 

lemma array_\<alpha>a_eq:
  "(xs = ys) \<longleftrightarrow> \<alpha>a xs = \<alpha>a ys"
  apply (rule iffI)
   apply (erule arg_cong[where f=\<alpha>a])
  apply (drule_tac x="\<alpha>a xs" and y="\<alpha>a ys" in arg_cong[where f=ArrayT.make])
  apply (simp add: array_make')
  done

lemma array_make_eq:
  "(xs = ys) \<longleftrightarrow> ArrayT.make xs = ArrayT.make ys"
  apply (rule iffI)
   apply (erule arg_cong[where f=ArrayT.make])
  apply (drule_tac x="ArrayT.make xs" and y="ArrayT.make ys" in arg_cong[where f=\<alpha>a])
  apply (simp add: array_make)
  done

end

