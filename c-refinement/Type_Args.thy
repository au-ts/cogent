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

theory Type_Args
imports "HOL-Word.Word"
begin
type_synonym funtyp = "char list"

(* Placeholder. We will need to add proper abstract value representations later on. *)
type_synonym abstyp = unit

(* FIXME this changes depending on L4V_ARCH ! *)
type_synonym ptrtyp = "32 word"

end
