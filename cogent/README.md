## Cogent Installation
------------------

Cogent builds with the Glasgow Haskell Compiler (GHC)

See [INSTALL.md](./INSTALL.md) for details.


## Command-line Options
--------------------

Run `cogent -?` to see the help message
`cogent --version` will print the git revision against which you build your Cogent compiler.

Run `. misc/cogent_autocomplete.sh` for bash auto-complete support. (The script requires an installed Cogent)


## Contents in This Directory
--------------------------
* [src/Cogent](./src/Cogent): Cogent compiler source code.
* [main](./main): The entry point for the Cogent compiler.
* [isa](./isa): Isabelle formalisation.
* [lib](./lib): C library for generated C code
* [Setup.hs](./Setup.hs): runhaskell entry.
* [doc](./doc): The Cogent compiler documentation.
* [misc](./misc): Miscellaneous helper scripts (Emacs/Vim syntax, Bash autocompletion, cabal.config files).
* [tests](./tests): Cogent test files.
* [examples](./examples): Some tiny but self-contained examples that newcomers should have a look.


## Known Issues
----------

* In Cogent, type constructors (type names) and data constructors (tags) don't share
the same namespace. In C parser/AutoCorres, however, they share the same 
namespace. Which means, if in Cogent, a type and a tag have the same name,
c-refinement proof will fail.

* If warnings are given by the typechecker, Isabelle embedding generation might
fail.

* Generating code with `--ffncall-as-macro` from non-ANF will cause problems. The
cause of the problem is our function calls are not truly function macros -- they
don't always obey macro's comma-parens separation rule.

* `'`s (read: primes) in Cogent identifiers will cause problem: Cogent will turn `'` to
`_prime` in generated C code but not in theory files, whereas C parser/AutoCorres
doesn't do the same trick.

* Trailing `_`s (read: underscores) in Cogent identifiers are problematic as well.
They are not consisdered good names in Isabelle.

* Bool type is defined as `u8` in generated C, with `1` being `True` and `0` `False`. This may
introduce inconsistency between Cogent semantics and C semantics. Extra care need be
taken when writing wrapper code.

* If a function signature is given in a `.cogent` file, but the corresponding definition
is not given in a `.ac` file, then Cogent compiler may not warn you.

* `$exp` antiquote is buggy. It seems to generate things as statements where expressions
are needed.

* Because Haskell is mostly non-strict, with some compiler command, it doesn't necessarily 
trigger compiler panic because the erroneous value is not (fully) evaluated.
`Deepseq` might be the cure. The difficulty is to define instances of `NFData`.

* `$exp` cannot call polymorphic functions, because the compiler has no way of knowing
what type instances are used by looking at the Cogent code. There is no easy cure. Cogent
compiler may need to *understand* the `.ac` files in order to check this. If poly-function
is called from `.ac` files, then it's very likely that the compiler will panic when
doing monomorphisation. The workaround is to define a wrapper function in a Cogent program
which calls and instantiates the poly-function.

* The `-entry-funcs` flag takes a file with a list of entry functions. These functions must
be monomorphic at the moment. This is unnecessary technically --- if we had a better parser
then we can easily allow poly-functions (instantiated, of course). This flag is only used in
monomorphisation phase and is large indenpendent of code generation or glue code. Current
workaround, as stated in the previous point, is to have wrapper functions in Cogent to
instantiate entry poly-functions. [TODO, LOW-HANGING]

* If any of the abstract Cogent functions is higher-order and the .ac file implements it, then
there must be at least one function which can serve as the argument to that higher-order
function, otherwise the generated C code will end up with undefined type (the type of the input
function).

* BE VERY CAREFUL potential trailing whitespaces in the --entry-funcs file! The parser does not
eliminate them and will be counted as part of the function name. [LOW-HANGING]
