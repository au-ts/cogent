# How To Run The QuickCheck Examples
---------------------------------------------------

## Setting up

_Assume `$PWD` is this directory._

1. Setup a cabal sandbox and install dependencies:
```
> cabal sandbox init
> cabal install --only-dependencies
```

2. Build QuickCheck Utils:
```
> cabal build cogent-quickcheck-utils
```

## Running the `WordArray` example

1. `cd wa_example; make; cd ../` which generates the C code and binary files.

2. `cabal build wa-example --ghc-options=" wa_example/build/wa.o"`

3. `cabal repl wa-example --ghc-options=" wa_example/build/wa.o"` which gives you a ghc REPL.

4. Inside the REPL, `$ GHCi > main` which runs all the tests.

5. For individual ones, `$ GHCi > quickCheck prop_corres_` and you can try to autocomplete the function names by tabbing the Tab key twice. 


## Running the `readpage` example

_Assume you have cabal-built `wa-example` as described above._

1. `cabal build readpage-example`

2. `cabal repl readpage-example` which gives you a ghc REPL.

3. Inside the REPL, `$ GHCi > Readpage.main` which runs the test using a default configuration.

4. If you want to run the test manually, then the property you are after is called `prop_corres_fsop_readpage`.
