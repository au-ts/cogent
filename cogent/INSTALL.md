# Cogent Installation Guide

## Dependencies

* `libgmp.so`
* `libncurses.so`
* [The Glasgow Haskell Compiler (GHC)](https://www.haskell.org/)
* [The Haskell Cabal](https://www.haskell.org/cabal/)
* [`alex`](https://www.haskell.org/alex/)
* [`happy`](https://www.haskell.org/happy/)
* [`z3`](https://github.com/Z3Prover/z3) (which is also included as a submodule for convenience)


## Installation Instructions

### Install Cogent dependencies

#### `libgmp` and `libncurses`
```
sudo apt-get install libgmp-dev	libncurses5-dev
```
or adapt it to the package manager of your choice.

#### The GHC compiler and Cabal

See [GHC download page](https://www.haskell.org/downloads) and [Cabal homepage](https://www.haskell.org/cabal/) for details.

_NOTE_: The supported versions of GHC and Cabal are specified [here](./cogent.cabal).

#### `alex` and `happy`
```
cabal install alex happy
```
Usually, the executables are located `$HOME/.cabal/bin/`. Make sure you add them to your `$PATH`.

#### `z3` SMT-solver

(_NOTE_: This is optional. You don't have to install `z3` if you don't plan to use Cogent's type-level computation features.)

Follow their [instructions](../z3/README.md). Make sure that the executable is included in your `$PATH`.

_NOTE_: We only tested against the snapshot checked-in in the [submodule](../z3). Similar versions of `z3`
have a chance to work but not guaranteed. We invoke `z3` via `sbv` package. You can find the `z3` versions that
are compatible with the `sbv` package you installed [on their github](https://github.com/LeventErkok/sbv/blob/master/SMTSolverVersions.md).


### Install Cogent

#### Build with Makefile

* To configure, edit [config.mk](../config.mk). The default values should work for most people.
* Copy the config file of the GHC version you want to use from [misc/cabal.config.d](./misc/cabal.config.d/)
to `./cabal.config` in this folder.
* Run `make` or `make dev`. The latter builds Cogent instead of installing it, which is
suitable for developers.

For more info, run `make help`.

#### Build with Cabal

The `Makefile` calls Cabal under the hood. It installs Cogent using a Cabal sandbox. If this
is not ideal for you (in rare cases), or you want to customise your installation further,
just use Cabal in the normal way. You need to install [isa-parser](../isa-parser) before you
build/install Cogent.

#### Build with Stack

[Stack](https://github.com/commercialhaskell/stack) is a new cross-platform
program for developing Haskell projects, that enhances the functionality
provided by Cabal. Unfortunately, several packages on which Cogent
depends are not supported by stack. For these reason, we don't officially
maintain a Stack build scheme.


## Test Cogent

1. Test files are in [./tests](./tests). Run `make` with relevant targets.

* `make tests` runs the entire test suite, which is NOT what you would like to do in most cases.
* There are individual tests that can be triggered by `make test-*`. See `make help` for details.
* `make examples` builds a group of small but complete Cogent examples.


2. Cogent compiler also comes with a small unit-test module. To run that, do this:
```
  $> cabal configure --enable-tests
  $> cabal build
  $> cabal test
```

