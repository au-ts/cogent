# Cogent Installation Guide

## Dependencies

* `libgmp.so`
* [The Glasgow Haskell Compiler (GHC)](https://www.haskell.org/)
* [The Haskell Cabal](https://www.haskell.org/cabal/)
* [`alex`](https://www.haskell.org/alex/)
* [`happy`](https://www.haskell.org/happy/)
* [`z3`](https://github.com/Z3Prover/z3) (which is also included as a submodule for convenience)


## Installation Instructions

### Install Cogent dependencies

#### The GHC compiler and Cabal

Follow the instructions on the [Haskell platform page](https://www.haskell.org/platform/) to install the Haskell Platform (which includes GHC and Cabal). It is sufficient to install Core.

_NOTE_: The supported versions of GHC and Cabal are specified [here](./cogent.cabal).

_NOTE_: On Linux you may also have to install `libgmp-dev`. This can be done with the command
```
sudo apt-get install libgmp-dev
```
or the equivalent command for your Linux distribution.

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

#### Optional features
Cogent comes with several experimental (reads: very unstable) or additional features that you can
opt-in. These features are (with the names of the respective flags in parentheses):
1. built-in static arrays (`builtin-arrays`)
2. documentation generation (`docgent`)
3. property-based testing in Haskell (`haskell-backend`)

Depending on which (combination of) features are needed, the dependencies will be different. By
default, none of them are enabled. If you want them enabled, appropriate flags should be given
while building Cogent (see below for instructions).


#### Build with Makefile

* To configure, edit [config.mk](../config.mk). The default values should work for most people.
* Copy the config file of the GHC version you want to use from [misc/cabal.config.d](./misc/cabal.config.d/)
into this folder, and then rename to `./cabal.config`.
* Run `make` or `make dev`. The latter builds Cogent instead of installing it, which is
suitable for developers.

For more info, run `make help`.

#### Build with Cabal

The `Makefile` calls Cabal under the hood. It installs Cogent using a Cabal sandbox. If this
is not ideal for you (in rare cases), or you want to customise your installation further,
just use Cabal in the normal way. You need to install [isa-parser](../isa-parser) before you
build/install Cogent.

To enable optional features, something like `--flags="flag1 flag2"` should be given when
`cabal configure` and `cabal install` are executed.

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

### Testing on macOS
To run Cogent examples and some tests, you need a GNU compatible version of `cpp` installed in your `PATH`. The default `cpp` installed on `macOS` isn't GNU compatible.

A solution:
1. Install Homebrew
2. Run `brew install gcc`. This will create symlinks `gcc-8` and `cpp-8` (or whatever the latest gcc version number is) in `/usr/local/bin` to the newly installed version of `gcc`.
3. Provided `ls /usr/local/bin/cpp` outputs `No such file or directory`, it should be safe to run `ln -s /usr/local/bin/cpp-8 /usr/local/bin/cpp`.
4. If `which cpp` doesn't print `/usr/local/bin/cpp`, then running `export PATH=/usr/local/bin:$PATH` in any shell where you want run the examples will ensure that the correct version of `cpp` is used.

Running `make examples` should now be successful.

