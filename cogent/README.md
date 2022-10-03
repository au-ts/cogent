## Cogent Installation
------------------

Cogent builds with the Glasgow Haskell Compiler (GHC)

See the [Installation Guide](https://cogent.readthedocs.io/en/latest/install.html) for details.


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
* [manual](./manual): A Cogent language manual.
* [misc](./misc): Miscellaneous helper scripts (Emacs/Vim syntax, Bash autocompletion, cabal.config files).
* [tests](./tests): Cogent test files.
* [examples](./examples): Some tiny but self-contained examples that newcomers should have a look.

