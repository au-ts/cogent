(*
This file is generated by Cogent
*)
theory Generated_ACInstall
imports
  "AutoCorres.AutoCorres"

begin


declare [[record_codegen = false]]
declare [[use_anonymous_local_variables=true]]
install_C_file "main_pp_inferred.c"
autocorres [keep_going, ts_rules = nondet, no_opt, skip_word_abs] "main_pp_inferred.c"

end

