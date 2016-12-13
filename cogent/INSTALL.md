# Cogent Installation Guide

## Dependencies

Cogent requires the Glasgow Haskell Compiler(GHC), and has been tested with the
following version of GHC:
* 7.10.1
* 7.10.2
* 7.10.3
* 8.0.1
* 7.8.4 (possibly)

### Installing Haskell Compiler

#### From Official Website
See https://www.haskell.org/downloads for information.

#### Commands for Installing Haskell Platform
```
wget 'https://haskell.org/platform/download/7.10.2/haskell-platform-7.10.2-a-unknown-linux-deb7.tar.gz'
tar -xzf haskell-platform-7.10.2-a-unknown-linux-deb7.tar.gz
sudo ./install-haskell-platform.sh
```

#### Instructions for Manual Installation
_NOTE_: It's *not* recommanded for users who are not familiar with Haskell's eco-system.

1. Install GHC (version 7.10.3 for example)
  * Download the right GHC distribution from https://www.haskell.org/ghc/download_ghc_7_10_3
  * Follow the instructions to install it (details omitted here)

2. Install cabal-install, and add `~/.cabal/bin` (or the directory in which cabal is installed) to your `$PATH`

  See https://www.haskell.org/cabal/download.html for details
  
_NOTE_:
 * Please install `cabal-install`, *not* `Cabal`; be sure that you have a proper version of `cabal-install` which 
   is compatible with your GHC version;
 * Old versions of `cabal-install` does not support sandbox. Please update to appropriate version (>= 1.18)
 * If `cabal-install` is built against an older version of Cabal, you might get
   a warning when you build Cogent. To solve it, when you have `cabal-install` installed, build again against
   a newer version of Cabal library.

### Other Dependencies

In addition to GHC, Cogent also requires `cabal-install`, for building and packaging.
(It's likely that `cabal-install` has been installed when you installed GHC)

Cogent has the following dependencies:
* [alex](https://www.haskell.org/alex/)
* [happy](https://www.haskell.org/happy/)

To install these dependencies, run:

`$ cabal install happy alex`

The following packages are needed by Cogent:
```
sudo apt-get install libgmp-dev libncurses-dev
```

## Installing Development Versions

If you intend to work with the latest development version, please consider
using Cabal sandboxes to minimise disruption to your local Haskell setup.
Instructions for doing so are available in [INSTALL-sandbox.md](./INSTALL-sandbox.md)

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

