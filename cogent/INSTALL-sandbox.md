# Install Cogent development version in a sandbox

This section describes how to install a development version of the Cogent compiler using
[cabal-sandboxes](https://www.haskell.org/cabal/users-guide/installing-packages.html#developing-with-sandboxes).

These instructions have been tested using Debian Jesse and will most likely apply equally well
to other distributions, provided the required versions of he Haskell compiler and dependencies
are properly installed.
To install the dependencies and make sure the enviroment complies with what is required,
please see the `Dependencies` section in (INSTALL.md)[./INSTALL.md].


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
