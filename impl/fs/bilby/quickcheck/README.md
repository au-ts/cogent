# How To Run The QuickCheck Examples
---------------------------------------------------

## Setting up

_Assume `$PWD` is this directory._

1. Make sure cabal-install-3.0 or above is used. To check, run
```
> cabal --version
```

2. Set environment variable:
```
> export COGENT_LIBGUM_DIR=<cogent-repo>/cogent/lib
```
where `<cogent-repo>` is the repository's top-level directory.

3. Build QuickCheck Utils:
```
> cabal build cogent-quickcheck-utils
```

## Running the `WordArray` example

1. `cd wa_example; make; cd ../` which generates the C code and binary files.

2. `cabal new-build wa-example --ghc-options="`pwd`/wa_example/build/wa.o"`

3. To run the tests:
```
> cabal new-build exe:wa-example-exe --ghc-options="`pwd`/wa_example/build/wa.o"
> cabal new-exec wa-example-exe
```
_NOTE: According to the [GHC user guide](https://downloads.haskell.org/ghc/latest/docs/users_guide/ghci.html#faq-and-things-to-watch-out-for), GHCi doesn't quite work with foreign functions.
Therefore we cannot run the tests interactively in GHCi [zilinc]_


## Running the `readpage` example

_Assume you have compiled `wa-example` as described above._

1. `cabal new-build readpage-example`

2. `cabal new-repl readpage-example` which gives you a ghc REPL.

3. Inside the REPL, `$ GHCi > Readpage.main` which runs the test using a default configuration.

4. If you want to run the test manually, then the property you are after is called `prop_corres_fsop_readpage`.

5. The Haskell embedding is pre-generated and manually modified to implement the abstract
Cogent types and functions, so you normally wouldn't want to regenerate it.
   But for whatever reason if you do want to generate your own, run
```
> cogent --hs-shallow-desugar-tuples readpage.cogent --flax-take-put
```
