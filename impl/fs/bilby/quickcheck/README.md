# How To Run The QuickCheck Examples
---------------------------------------------------

## Setting up

_Assume `$PWD` is this directory._

1. Make sure cabal-install-3.0 or above is used. To check, run
```
> cabal --version
```

2. Build QuickCheck Utils:
```
> cabal build cogent-quickcheck-utils
```

## Running the `WordArray` example

1. `cd wa_example; make; cd ../` which generates the C code and binary files.

2. `cabal new-build wa-example --ghc-options="`pwd`/wa_example/build/wa.o"`

3. To run the tests, run
```
> cabal new-build exe:wa-example-exe --ghc-options="`pwd`/wa_example/build/wa.o"
> cabal new-exec wa-example-exe
```
_NOTE: I cannot get cabal new-repl to work with linking. Hope someone can work it out. [zilinc]_

[If someone can manage to launch the REPL:]

4. Inside the REPL, `$ GHCi > main` which runs all the tests.

5. For individual ones, `$ GHCi > quickCheck prop_corres_` and you can try to autocomplete the function names by tabbing the Tab key twice. 


## Running the `readpage` example

_Assume you have cabal-built `wa-example` as described above._

1. `cabal new-build readpage-example`

2. `cabal new-repl readpage-example` which gives you a ghc REPL.

3. Inside the REPL, `$ GHCi > Readpage.main` which runs the test using a default configuration.

4. If you want to run the test manually, then the property you are after is called `prop_corres_fsop_readpage`.

5. The Haskell embedding is pre-generated and manually modified, so you normally wouldn't want to regenerate it.
   But for whatever reason if you do want to generate your own, run
```
> export COGENT_LIBGUM_DIR=<your libgum location>
> cogent --hs-shallow-desugar-tuples readpage.cogent --flax-take-put
```
