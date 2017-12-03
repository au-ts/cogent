theory Scratch

imports "AutoCorres"

begin

declare [[record_codegen = false]]
declare [[use_anonymous_local_variables=false]]
install_C_file "array_crefine.c"
autocorres [keep_going, ts_rules = nondet, no_opt, skip_word_abs] "test.c"

find_theorems name: "test.foo"

thm test.foo'_def test.bar'_def test.quux'_def

end