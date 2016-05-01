(*
 * Copyright 2016, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(NICTA_GPL)
 *)

theory RbtT
imports
  "../adt/BilbyT"
begin
text {* Red-black tree axiomatization *}

consts \<alpha>rbt :: "('k,'v) Rbt \<Rightarrow> ('k \<rightharpoonup> 'v)"

axiomatization
where
  rbt_get_value_ret:
  "rbt_get_value (rbt, key) = (case \<alpha>rbt rbt key of option.Some v \<Rightarrow> Success v | option.None \<Rightarrow> Error ())"

end