(*
 * Copyright 2016, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(NICTA_GPL)
 *)

theory Read_Table
imports
  "../cogent/isa/Cogent"
  Specialised_Lemma_Utils
begin

(*
 * Read Cogent-C type mapping (".table" file) generated by cogent compiler.
 * The format is:
 *   Cogent_type :=: C_type
 * e.g.
 *   TRecord [(TPrim (Num U32), False)] Unboxed :=: t1
 * We parse each pair by reading Cogent_type as an Isabelle term.
 * C_type is a C identifier so parsing it is trivial.
 *)

ML {*
fun read_table (file_name:string) thy =
  let
    val path_to_c = (Resources.master_directory thy |> File.platform_path) ^ "/" ^ file_name;
    val path_to_table = (unsuffix ".c" path_to_c) ^ ".table";
    val input_file = TextIO.openIn path_to_table;

    val lines = split_lines (TextIO.inputAll input_file);
    val pos_lines = (1 upto length lines) ~~ lines;
    fun report pos = path_to_table ^ ":" ^ string_of_int pos ^ ": ";

    val tymap = pos_lines
                |> filter (fn (pos, l) => not (String.isPrefix "--" l) andalso
                                          not (String.isPrefix " " l) andalso
                                          not (String.size l = 0))
                |> map (fn (pos, l) =>
                    case split_on " :=: " l of
                        [cogentT, cT] => (pos, cogentT, cT)
                      | _ => error (report pos ^ "expected \" :=: \""))
                : (int * string * string) list;

    val ctxt = Proof_Context.init_global thy
    val tymap = tymap
                |> map (fn (pos, cogentT, cT) => let
                    fun err () = error (report pos ^ "failed to parse Cogent type")
                    val cogentT = Syntax.read_term ctxt cogentT
                                handle ERROR _ => err ()
                    val _ = if type_of cogentT = @{typ Cogent.type} then () else err ()
                    in (pos, cogentT, cT) end)
                : (int * term * string) list;

    fun decode_sigil _   (Const (@{const_name Writable}, _)) = Writable
      | decode_sigil _   (Const (@{const_name ReadOnly}, _)) = ReadOnly
      | decode_sigil _   (Const (@{const_name Unboxed},  _)) = Unboxed
      | decode_sigil pos t = raise TERM (report pos ^ "bad sigil", [t]);

    fun decode_type (pos, Const (@{const_name TCon}, _) $ _ $ _ $ sigil, cT) =
            UAbstract cT
      | decode_type (pos, Const (@{const_name TRecord}, _) $ _ $ sigil, cT) =
            URecord (cT, decode_sigil pos sigil)
      | decode_type (pos, Const (@{const_name TSum}, _) $ variants, cT) =
            USum (cT, variants)
      | decode_type (pos, Const (@{const_name TProduct}, _) $ _ $ _, cT) =
            UProduct cT
      | decode_type (pos, t, cT) =
            raise TERM (report pos ^ "unrecognised type", [t]);

    val uvals = map decode_type tymap |> rm_redundancy
   in
    uvals
   end : uval list;
*}
end
