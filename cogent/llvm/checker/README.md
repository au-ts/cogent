# Cogent to VIR (Vellvm) Compiler

## Requirements

* Coq 8.12.x
* Vellvm's [requirements](https://github.com/vellvm/vellvm/#assumes)
    - `coq-ext-lib`
    - `coq-paco`
    - `coq-flocq`
    - `coq-ceres`
    - `coq-mathcomp-ssreflect`
    - `coq-simple-io`
    - `dune`
    - `menhir`
    - `qcheck`
* A subset of Helix's [requirements](https://github.com/vzaliva/helix#dependencies):
    - `coq-color`
    - `coq-libhyps`
    - `coq-math-classes`

## Compilation

1. Ensure the `vellvm` submodule is **recursively** cloned
2. Compile the `vellvm` dependency: `make -C vellvm/src`
3. Build the compiler: `make`

## Using the extracted Haskell

After compilation, `extracted/Compiler.hs` can be used by the core Cogent compiler to produce VIR. A Haskell module has been created to allow this to be used with the original Cogent AST and the llvm-hs library. The Cogent compiler flag to use this module is currently `--llvm-coq` .

## Running the compiler or semantics with Coq

It may be easier in some cases to test the Coq-based backend independently. `coq/Test.v` has an example of how one could compile an AST provided in a `.v` file, or run the interpreter over its ITree semantics. The `--coq-gen` flag of the Cogent compiler will aid in producing the `.v` file containing the AST for a given Cogent program.

LLVM IR can also be converted into a `.v` file containing the corresponding VIR AST using the `parse_ll` script which is a wrapper around the Vellvm binary.
