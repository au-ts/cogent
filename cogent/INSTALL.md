# Cogent Installation Guide

## Dependencies

Cogent requires the Glasgow Haskell Compiler(GHC), and has been tested with the
following version of GHC:
* 7.10.1
* 7.10.2
* 7.8.3 (possibly)

In addition to GHC, Cogent also requires `cabal-install`, for building and packaging.

Cogent has the following dependencies:
* [alex](https://www.haskell.org/alex/)
* [happy](https://www.haskell.org/happy/)

To install these dependencies, run:

`$ cabal install happy alex`

## Installing Development Versions

If you intend to work with the latest development version, please consider
using Cabal sandboxes to minimise disruption to your local Haskell setup.
Instructions for doing so are available in (INSTALL-sandbox.md)[./INSTALL-sandbox.md]

To configure, edit config.mk. The default values should work for most people.

Cogent is built using a Makefile:

* `make` - will build and install everything in your local `dist` directory.
* `make test` - will run the test suite.
* `make bench` - will run the benchmarks.

## Building with Stack

[Stack](https://github.com/commercialhaskell/stack) is a new cross-platform
program for developing Haskell projects, that enhances the functionality
provided by Cabal. There is experimental support for building Cogent with Stack.

To build Cogent with Stack, run the following command:

* `stack build`

This will install Cogent, and all the related files in `./local/bin` on Linux.
If you haven't configured already, there might be some configuration/setup related
to Stack that might be required.
