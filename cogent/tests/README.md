# Cogent Test Infrastructure

## Writing tests

Place your test in the relevent folder (or make a new one), and write a `config.yaml` file for your test.

Config files can be placed anywhere below the testing directly, as long as the test files (`*.cogent` files) are in the same directory.

## Configuration file structure

Each configuration file is a YAML file that starts with one root field called `test`. This field contains a list of tests each with the following structure:

```yaml
# A list of files to test. Can contain one or more test files
files: 
  - FILE.cogent
  - [ FILE.cogent ... ]

# A list of one or more flags to be given to the Cogent compiler
flags:
  - FLAG
  - [ FLAG ... ]

# The expected test result. 
# "yes" means the file should successfully compile.
# "no" means the compiler should successfully finish, 
#   but the code shouldn't compile.
# "error" means the compiler is expected to crash 
#   (useful for tests that are currently broken).
shouldpass: "yes" | "no" | "error"
```

## Test script arguments

Run the script with `-h` or `--help` for a more detailed explanation.

* `--verbose [FILES]` gives verbose output for the tests provided, or all tests if no files are supplied
* `--only [FILES]` runs the tests for the files provided

## Dependancies

The test script depends on the following python modules:
* [ruamel](https://yaml.readthedocs.io/en/latest/)
* [termcolor](https://pypi.org/project/termcolor/)