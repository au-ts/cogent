# Install Cogent development version in a sandbox

This section describes how to install a development version of the Cogent compiler using
[cabal-sandboxes](https://www.haskell.org/cabal/users-guide/installing-packages.html#developing-with-sandboxes).

These instructions have been tested using Debian Jesse and will most likely apply equally well
to other distributions, provided the required versions of he Haskell compiler and dependencies
are properly installed.
To install the dependencies and make sure the enviroment complies with what is required,
please see the `Dependencies` section in [INSTALL.md](./INSTALL.md).


### Initialise sandbox

In the Cogent repository, run the following commands:

```
$ cd cogent

$ cabal sandbox init

$ cabal sandbox add-source ../isa-parser

```

### Install dependencies

The following command lists the dependencies that Haskell will install during installation
of Cogent:

`$ cabal install --dry-run --only-dependencies`

To actually install the dependencies, run:

`$ cabal install --only-dependencies`


### Build Cogent

```
$ cabal configure

$ cabal build
```

Running the above commands will make the `cogent` compiler available in `./dist/build/cogent`.


### Install Cogent

To install `Cogent` in the sandbox, run:

`$ cabal install`


### Using Cogent

After installing, the `Cogent` compiler will be available in `.cabal-sandbox/bin` and can be
run as:

```
$ ./.cabal-sandbox/bin/cogent
```

Adding the above path to the `PATH` environment variable will make sure it is available for
general development.


### Troubleshooting

1. You might get an error about missing alex and/or happy. Just do `cabal install alex happy`.
   They will be installed to `~/.cabal/bin`. Make sure this directory is in your `$PATH`.
2. You might also get an error while install hcurses. You would need to install libncurses5-dev on
   debian/ubuntu (or equivalents on your platform).
3. `cabal build` will build executable file in `./dist/build/cogent/` whereas `cabal install`
   will put the executable in the sandbox.
4. You might get the error "ghc no longer supports single-file style package databases".
   This trick worked for me: remove your `dist` directory and run `ghc-pkg init dist`
5. Due to some unknown GHC bug, linking might take extremely long. To solve it, you can either
  - create a `cabal.config` file (if you don't have one) in your `cogent` folder, put the following 
     line into the file:
```
executable-dynamic: True
```
  - add `--enable-executable-dynamic` flag to `cabal configure`. You may need `cabal clean` first. 

