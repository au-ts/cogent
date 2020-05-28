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

(*
 The cogent_C_val class provides val_rel and type_rel,
 generic predicates for matching Cogent and C values and types.
 This file also gives program-independent instances for cogent_C_val.
 *)
theory Value_Relation
  imports
    "HOL-Word.Word"
    "AutoCorres.AutoCorres"
    "Cogent.UpdateSemantics"
begin

type_synonym funtyp = "char list"

type_synonym ptrtyp = addr

(* Placeholder. We will need to add proper abstract value representations later on. *)
datatype atyp =  WAU32 "32 word" "32 word" | TOther
type_synonym abstyp = atyp

(* Mechanism to get different instances of cogent_C_val for signed and unsigned words. *)
class knows_sign = fixes is_signed :: "'a itself \<Rightarrow> bool"

instantiation signed :: (type) knows_sign begin
  definition is_signed_signed_def:
    "is_signed (_ :: 'a signed itself) = True"
  instance ..
end

instantiation bit0 :: (type) knows_sign begin
  definition is_signed_bit0_def:
    "is_signed (_ :: 'a bit0 itself) = False"
  instance ..
end

instantiation bit1 :: (type) knows_sign begin
  definition is_signed_bit1_def:
    "is_signed (_ :: 'a bit1 itself) = False"
  instance ..
end

class cogent_C_val = c_type +
  fixes val_rel :: "(funtyp, abstyp, ptrtyp) uval \<Rightarrow>'a \<Rightarrow> bool"
  fixes type_rel :: "repr \<Rightarrow> 'a itself \<Rightarrow> bool"

(* The signed word relation is the relation for function tags, so we can only
 * define it after reading the program.
 * Here is a hack to defer this task. *)
consts cogent_function_val_rel :: "(funtyp, abstyp, ptrtyp) uval \<Rightarrow> int \<Rightarrow> bool"
consts cogent_function_type_rel :: "repr \<Rightarrow> 'a word itself \<Rightarrow> bool"

instantiation word :: ("{len8, knows_sign}") cogent_C_val
begin
  definition type_rel_word_def:
    "type_rel a (t :: 'a word itself) \<equiv>
       if is_signed TYPE ('a) then cogent_function_type_rel a t
       else (
       if      len_of TYPE('a) = 64 then a = RPrim (Num U64)
       else if len_of TYPE('a) = 32 then a = RPrim (Num U32)
       else if len_of TYPE('a) = 16 then a = RPrim (Num U16)
       else if len_of TYPE('a) =  8 then a = RPrim (Num U8)
       else False)"

  definition val_rel_word_def:
    "val_rel uv (x :: 'a word) \<equiv>
       if is_signed TYPE('a) then cogent_function_val_rel uv (sint x) else
       if      size x = 64 then uv = UPrim (LU64 (ucast x))
       else if size x = 32 then uv = UPrim (LU32 (ucast x))
       else if size x = 16 then uv = UPrim (LU16 (ucast x))
       else if size x =  8 then uv = UPrim (LU8  (ucast x))
       else False"

  instance ..
end

lemmas is_signed_simps = is_signed_signed_def is_signed_bit0_def is_signed_bit1_def
lemmas val_rel_word64 = val_rel_word_def [where 'a=64, simplified word_size ucast_id is_signed_simps, simplified]
lemmas val_rel_word32 = val_rel_word_def [where 'a=32, simplified word_size ucast_id is_signed_simps, simplified]
lemmas val_rel_word16 = val_rel_word_def [where 'a=16, simplified word_size ucast_id is_signed_simps, simplified]
lemmas val_rel_word8  = val_rel_word_def [where 'a= 8, simplified word_size ucast_id is_signed_simps, simplified]
lemmas val_rel_word = val_rel_word64 val_rel_word32 val_rel_word16 val_rel_word8

lemmas val_rel_fun_tag = val_rel_word_def [where 'a="32 signed", simplified is_signed_simps, simplified]

lemmas type_rel_word64 = type_rel_word_def [where 'a=64, simplified is_signed_simps, simplified]
lemmas type_rel_word32 = type_rel_word_def [where 'a=32, simplified is_signed_simps, simplified]
lemmas type_rel_word16 = type_rel_word_def [where 'a=16, simplified is_signed_simps, simplified]
lemmas type_rel_word8  = type_rel_word_def [where 'a= 8, simplified is_signed_simps, simplified]
lemmas type_rel_word = type_rel_word64 type_rel_word32 type_rel_word16 type_rel_word8

lemmas type_rel_fun_tag = type_rel_word_def [where 'a="32 signed", simplified is_signed_simps, simplified]

instantiation unit :: cogent_C_val
begin
  definition type_rel_unit_def:
    "type_rel typ (_ :: unit itself) \<equiv> typ = RUnit"
  definition val_rel_unit_def:
    "val_rel uv (x :: unit) \<equiv> uv = UUnit"
  instance ..
end

instantiation ptr :: (cogent_C_val) cogent_C_val
begin
  definition val_rel_ptr_def:
    "val_rel uv (x :: 'a ptr) \<equiv> \<exists>repr. uv = (UPtr (ptr_val x) repr)"
  definition type_rel_ptr_def:
    "type_rel typ (_:: 'a ptr itself) \<equiv> \<exists>repr. typ = RPtr repr \<and> type_rel repr TYPE('a)"
  instance ..
end

end
