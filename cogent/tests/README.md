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
# A list of files to test. Can contain one or more test files
- { 
  test_name: sample-test
  files: 
    - FILE.cogent
    - [ FILE.cogent ... ]

  # The expected test result. 
  # "pass" means the file should successfully compile or
  #   the test should successfully run
  # "fail" means the compiler should successfully finish, 
  #   but the code shouldn't compile successfully or the test failed
  # "error" means the compiler is expected to crash 
  #   (useful for tests that are currently broken).
  # "wip" means the test hasn't been completed.
  #   It will be run and the output will be ignored and marked as passing
  expected_result: ( "pass" | "fail" | "error" | "wip" )
}
- { ... }
```

There are 3 testing methods the script supports:
  1. directly running the cogent compiler by specifying the command-line flags;
  2. running a "phase", usually verification, according to a phase script file;
  3. running arbitrary commands.

Each test supports only ONE of these commands at once.

### Testing Compiler By Flags

To test compiler output, include the `flags` field in a test dictionary, which is a list of flags to pass to the compiler.

The use of the `--dist-dir` flag is not supported and will cause an error if supplied, as the test script needs to use this flag to send compiler output to an isolated location.

If we wanted to test a single Cogent file up to typechecking with pretty error messages, and we expect this test to pass, we can make the following test configuration:

```yaml
- test_name: example
  files: 
    - example.cogent
  flags:
    - "--fpretty-errmsgs"
    - "--typecheck"
  expected_result: pass
```

### Testing An Extra Phase of The Compiler

When running the test script, a `--extra-phases` flag needs to be passed,
designating where the extra phase description files are located.
For each test group, all test files will run against the "phase" to be tested. For example:
```
- test_name: type-proof
  files:
    - pass_simple-1.cogent
    - pass_complex-1.cogent
  expected_result: pass
  phase: type_proof
```
This relies on that fact that in the `phases` directory, which will be passed in
via `--extra-phases`, there is a script called `type_proof.sh`. This script
intructs the test driver what needs to run.


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
- test_name: verification 
  files:
    - verificationTest.cogent
  verification: 
    stage: "AllRefine"
    types: "types.cfg"
    entryfuncs: "entryfuncs.cfg"
    autocorres: "/home/user/autocorres"
  expected_result: "fail"
```

### Running Arbitrary Commands

To run an arbitrary script as a test, supply the field `run` which contains a list of strings
that will be executed in the shell. If the command returns `0` as it's exit code, the test
succeeds. Otherwise, the test fails. It's a lighter form of "phase" test.

If the file name in `files` is a directory, the commands will be antomatically
run inside that directory; otherwise it will be run from the current directory which contains the config.yaml file.

The `error` value in the field `expected_result` is not supported for this method of testing.

The following example runs a provided script, which is expected to fail (i.e. expecting the script to return a non-0 exit code):

```yaml
- test_name: script-test
  files:
      - pass_antiquoted-c
  run: 
      - bash BUILD
  expected_result: "fail"
```

## Test script arguments

Run the script with `-h` or `--help` for a more detailed explanation.

* `--verbose [FILES]` gives verbose output for the tests provided, or all tests if no files are supplied
* `--only [FILES]` runs the tests for the files provided
* `--ignore-phases` removes particular "phases" from a test run. In particular, if
the phase is "cogent", it will ignore all tests that are compiler-centric, i.e. those
specified using the `flags` field.

## Dependancies

The test script depends on the following python modules:
* [ruamel.yaml](https://yaml.readthedocs.io/en/latest/)
* [termcolor](https://pypi.org/project/termcolor/)

## Future improvements/feature suggestions

* Give clusters/groups of tests a name so they can be run by name
* Only run one config file
