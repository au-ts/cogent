(*
 * Copyright 2016, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(NICTA_GPL)
 *)

theory Specialised_Lemma
imports
  Specialised_Lemma_USum
  Specialised_Lemma_URecord
begin

context update_sem_init 
begin

ML{* fun mk_lems file_nm ctxt  =
 let
  val thy = Proof_Context.theory_of ctxt;
  val uvals                 = read_table file_nm thy;
  val num_of_uvals          = List.length uvals;
  fun get_nth_uval nth      = List.nth (uvals, nth);
  fun get_urecord_lems uv   = mk_urecord_lems_for_uval file_nm ctxt uv;
  fun get_case_lems uv      = mk_case_lems_for_uval file_nm ctxt uvals uv;
  val (lemss:lem list list) = List.tabulate (num_of_uvals, fn struct_num =>
    (tracing ("mk_lems started working on mk_specialised for struct_number " ^ string_of_int struct_num ^ 
              " which corresponds to " ^ (*@{make_string}*) get_ty_nm_C (get_nth_uval struct_num));
    case get_nth_uval struct_num of 
      URecord _ => get_urecord_lems (get_nth_uval struct_num)
    | USum    _ => get_case_lems    (get_nth_uval struct_num)
    | _         => []));
 in
  List.concat lemss
   |> map (fn v => (#name v, v))
   |> Symtab.make_list |> Symtab.dest
   |> map (fn (nm, xs) => let
       val fst_x = hd xs;
       val _ = map (fn x => (#prop x aconv #prop fst_x) orelse 
             raise TERM ("lemmas: non duplicate for " ^ nm, [#prop x, #prop fst_x])) xs
       (* Why does Thomas want to have duplicate !? *)
      in hd xs end
    )
 end;
*}

ML{* (* local_setup_take_put_member_case_esac_specialised_lemmas *)
local 

fun prove_put_in_bucket_non_esac_especialised_lemma ((lem:lem), lthy:local_theory) =
(* This function does not handle specialised lemmas for Esac, 
   since they are generated by forward-reasoning.*)
 let
  val (lem_name, bucket, prop, mk_tac) = (#name lem, #bucket lem, #prop lem, #mk_tactic lem);

  (* We want to have schematic variables rather than fixed free variables after registering this lemma.*)
  val names = Variable.add_free_names lthy prop [];

  fun get_tac ctxt = if Config.get ctxt cheat_specialised_lemmas 
                     then Skip_Proof.cheat_tac ctxt 1
                     else mk_tac ctxt;
  val some_thm = (SOME (Goal.prove lthy names [] prop (fn {context, prems} => (get_tac context)))) 
                 handle ERROR _ => NONE;
  (* If proof goes well, register the proved lemma and putting it in the corresponding bucket.
   * If not, add the name of the thm in Unborn_Thms. *)
  val lthy = if   is_some some_thm 
             then Local_Theory.note ((Binding.name lem_name, []), [the some_thm]) lthy |> snd |>
                  local_setup_add_thm bucket (the some_thm)
             else Local_Theory.target (add_unborns lem_name) lthy;
 in
  lthy
 end;

fun local_setup_tag_enum_defs lthy =
(* Warning! The author of this function has no clue as to how tag_t_defs are created
 * by C-Parser. If C-Parser changes its naming scheme, this code stops working properly.*)
 let
  val thms = Proof_Context.get_thms @{context} "tag_t_defs" 
            handle ERROR msg  => (tracing msg; @{thms TrueI})
  val lthy' = Local_Theory.note ((Binding.name "tag_enum_defs",[]), thms) lthy |> snd
 in
  lthy'
 end;

in

fun local_setup_take_put_member_case_esac_specialised_lemmas file_nm lthy =
 let 
  val lems:lem list = mk_lems file_nm lthy;
  val lthy_wo_esac  = List.foldl prove_put_in_bucket_non_esac_especialised_lemma lthy lems;
  val lthy_w_esac   = local_setup_specialised_esacs file_nm lthy_wo_esac;
  val lthy'         = local_setup_tag_enum_defs lthy_w_esac;
  val lthy''        = local_setup_put_lemmas_in_bucket lthy';
 in
  lthy''
 end;

end
*}

end

end
