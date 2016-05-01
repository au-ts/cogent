(*
 * Copyright 2016, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(NICTA_GPL)
 *)

theory Type_Args
imports Main
        "~~/src/HOL/Word/Word"
begin
type_synonym funtyp = "char list"

(* Placeholder. We will need to add proper abstract value representations later on. *)
type_synonym abstyp = unit

type_synonym ptrtyp = "32 word"

end
