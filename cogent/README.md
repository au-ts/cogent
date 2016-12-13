## Cogent Installation
------------------

Cogent builds with the Glasgow Haskell Compiler (GHC)

Tested with GHC-7.10.3 and GHC-8.0.1. Similar versions have a chance to work.

See [INSTALL.md](./INSTALL.md) for details.


## Command-line Options
--------------------

Run `cogent -?` to see the help message
`cogent --version` will print the git revision against which you build your Cogent compiler.


## Testing
-------

1. Run `./validate` (with appropriate arguments) to test Cogent compiler. Test files are in `./tests`

2. Cogent compiler also comes with a small unit-test module. To run that, do this:
```
  $> cabal configure --enable-tests
  $> cabal build
  $> cabal test
```
Note: You might run into this problem: "You need to re-run the 'configure' command".
      For more info, see https://github.com/haskell/cabal/issues/2214


## Contents in This Directory
--------------------------
* [src/Cogent](./src/Cogent): Cogent compiler source code.
* [main](./main): The entry point for the Cogent compiler.
* [isa](./isa): Isabelle formalisation.
* [lib](./lib): C library for generated C code
* [Setup.hs](./Setup.hs): runhaskell entry.
* [doc](./doc): The Cogent compiler documentation.
* [misc](./misc): Miscellaneous helper scripts(Emacs/Vim syntax and Bash autocompletion files)
* [tests](./tests): Cogent test files.


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
doing monomorphisation. The workaround is to define a wrapper function in a cogent program
which calls and instantiates the poly-function.

