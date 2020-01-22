# Cogent Test Infrastructure

## Test script output

The test script will output all tests results, and whether tests passed, failed or errored.

The script returns `1` if any unexpected failures or errors occured, and `0` otherwise.

In the event of an unexpected failure or error, the compiler output will be printed below the test.

## Writing tests

Place your test in any folder that is a subdirectory of the directory that contains the testing script, and write a `config.yaml` file for your test. This config file MUST be placed in the same directory of the Cogent files it tests.

## Configuration file structure

Each configuration file is a YAML file that starts with one root field called `test`. This field contains a list of tests, with the overall structure shaped like this:

```yaml
test:
    # A list of files to test. Can contain one or more test files
  - { 
    files: 
      - FILE.cogent
      - [ FILE.cogent ... ]

    # The expected test result. 
    # "yes" means the file should successfully compile.
    # "no" means the compiler should successfully finish, 
    #   but the code shouldn't compile successfully.
    # "error" means the compiler is expected to crash 
    #   (useful for tests that are currently broken).
    # "wip" means the test hasn't been completed.
    #   it will be run and the output will be ignored and marked as passing
    expected_result: ( "pass" | "fail" | "error" | "wip" )
  }
  - { ... }
```

There are 3 testing methods the script supports; Observing compiler output, verification output, and running an arbitrary command. Each test supports only ONE of these commands at once.

### Testing compiler output

To test compiler output, include the `flags` field in a test dictionary, which is a list of flags to pass to the compiler.

The use of the `--dist-dir` flag is not supported and will cause an error if supplied, as the test script needs to use this flag to send compiler output to an isolated location.

If we wanted to test a single Cogent file up to typechecking with pretty error messages, and we expect this test to pass, we can make the following test configuration:

```yaml
test:
  - files: 
      - example.cogent
    flags:
      - "--fpretty-errmsgs"
      - "--typecheck"
    expected_result: "yes"
```

### Testing Verification Output

**CURRENTLY NOT SUPPORTED**

Verification testing will compile and then build a generated isabelle file. ALL verification files will be generated, however only the specified file will be run.

To test generated verification files, supply a field `verification` that contains the following fields:
* `stage`, the generated file that verification should be run on, which contains one of the following values:
  * `ACInstall`
  * `AllRefine`
  * `CorresProof`
  * `CorresSetup`
  * `Deep_Normal`
  * `MonoProof`
  * `NormalProof`
  * `SCorres_Normal`
  * `ShallowConsts_Desugar`
  * `ShallowConsts_Desugar_Tuples`
  * `Shallow_Desugar`
  * `Shallow_Desugar_Tuples`
  * `Shallow_Normal`
  * `ShallowShared`
  * `ShallowShared_Tuples`
  * `ShallowTuplesProof`
  * `TypeProof`
* Optionally `types`, the path of a file which will be given as input to the `--ext-types` flag
* Optionally `entryfuncs`, the path of a file which will be given as input to the `--entry-funcs` flag
* Optionally `autocorres`, the path of the AutoCorrs directory. Running any files that use or depend on a file that uses AutoCorres requires this flag to be present.

Here's an example configuration that runs verification on the generated AllRefine file of a Cogent program:

```yaml
test:
  - files:
      - verificationTest.cogent
    verification: 
      stage: "AllRefine"
      types: "types.cfg"
      entryfuncs: "entryfuncs.cfg"
      autocorres: "/home/user/autocorres"

    expected_result: "no"
```

### Running Arbitrary Tests

**CURRENTLY NOT SUPPORTED**

To run an arbitrary script as a test, supply the field `command` which contains a string
that will be executed in the shell. If the command returns `0` as it's exit code, the test
succeeds. Otherwise, the test fails.

The `error` value in the field `expected_result` is not supported for this method of testing.

Note that the `files` field is still necessary as they are used to name the test, however the files themselves need not exist.

The following example runs a provided script, which is expected to fail (i.e. expecting the script to return a non-0 exit code):

```yaml
test:
  - files:
      - scriptTest.cogent
    command: "L4V_ARCH=ARM ./testScript.sh"
    shouldpass: "no"
```

## Test script arguments

Run the script with `-h` or `--help` for a more detailed explanation.

* `--verbose [FILES]` gives verbose output for the tests provided, or all tests if no files are supplied
* `--only [FILES]` runs the tests for the files provided

## Dependancies

The test script depends on the following python modules:
* [ruamel](https://yaml.readthedocs.io/en/latest/)
* [termcolor](https://pypi.org/project/termcolor/)