#!/usr/bin/env python3

from termcolor import colored
from ruamel.yaml import YAML
from ruamel.yaml.scanner import ScannerError
import os
import subprocess
import sys
import importlib
import re
import shutil
import argparse
from collections import OrderedDict
from pathlib import Path

# Check version is at least python 3.7
if sys.version_info[0] < 3:
    print(">= python 3.6 is required to run the testing script")
    print("Your version: {0}.{1}.{2}".format(
        sys.version_info[0], sys.version_info[1], sys.version_info[2]))
    sys.exit(1)


PYTHON_V37 = sys.version_info[0] == 3 and sys.version_info[1] >= 7

# Check all our dependancies are installed


def check_import(name):
    try:
        importlib.import_module(name)
        return True
    except ImportError as exc:
        print("Dependancy module '{}' not installed - please install via pip3".format(name))
        return False


importok = [check_import("ruamel.yaml"), check_import("termcolor")]

if not all(importok):
    sys.exit(1)


CONFIG_FILE_NAME = "config.yaml"
TEST_DIST_DIR = os.path.join(os.path.dirname(
    os.path.realpath(__file__)), "dist")


def clean_dist():
    # rm -rf
    shutil.rmtree(TEST_DIST_DIR, ignore_errors=True)


def setup_dist():
    if os.path.exists(TEST_DIST_DIR):
        clean_dist()
    os.mkdir(TEST_DIST_DIR)


# Dodgy: A global list of test names that should be verbose
# if it is None, then verbose is off
# if it is empty, that means all tests should be verbose
# if it is nonempty, only the test names inside should be verbose
verbose_test_names = None

# Represents the result of a test
# Takes in a function which returns
#   (status, errormsg, expected)
# where status, expected :: "pass" | "fail" | "error" | "wip"


class TestResult:

    block_len = 15

    def __init__(self, test, fullname, test_name):
        self.test = test
        self.fullname = fullname
        self.test_name = test_name
        self.display()

    def result(self):
        (status, _, expected) = self.test
        return status == expected or expected == "wip"

    # Printing test results
    def display(self):

        acc = ""
        print("{}: ".format(os.path.relpath(self.fullname)), end="")
        (status, output, expected) = self.test

        be_verbose = (verbose_test_names is not None and 
                                (verbose_test_names == [] or
                                 self.test_name in verbose_test_names))


        if expected == "wip":
            acc += colored("WIP (Pass by defualt)\n", "green")
        elif status == "error" and expected != "error":
            acc += colored("Error? ", "yellow") + "Reason:\n"
        elif status == expected:
            if status == "pass":
                acc += colored("Passed\n", "green")
            elif status == "fail":
                acc += colored("Failed (as expected)\n", "green")
            elif status == "error":
                acc += colored("Error (as expected)\n", "green")
        else:
            if expected == "error":
                acc += coloured("Test ran but was expected to error", "red")
            elif expected == "pass":
                acc += colored("Failed", "red") + "\n"
            elif expected == "fail":
                acc += colored("Failed (expected fail, got pass)",
                               "red") + "\n"

        if be_verbose or (status != expected and expected != "wip"):
            acc += ("=" * self.block_len + "Test Output" +
                    "=" * self.block_len) + "\n"
            acc += output
            acc += ("=" * self.block_len + len("Test Output")
                    * "=" + "=" * self.block_len) + "\n"

        print(acc, end="")
        return (status == expected) or expected == "wip"

# For validating configurations


class InvalidConfigError(Exception):
    pass

# Represents a test configuration file
# Can perform multiple actions according to the layout of the file


class TestConfiguration:

    valid_test_fields = ["files", "expected_result", "test_name"]
    valid_test_types = ["flags", "command", "verification"]

    header_block_len = 20

    # file path must be ABSOLUTE
    def __init__(self, filepath):
        with open(filepath, 'r') as f:
            self.settings = YAML().load(f.read())
            self.filepath = filepath
            self.relpath  = os.path.relpath(self.filepath)
            self.dir = os.path.dirname(filepath)
            self.validate_config()

    # Checks a given config file is valid
    def validate_config(self):
        if (not isinstance(self.settings, list)):
            raise InvalidConfigError(
                "{}: Config files must be a list of test objects".format(self.relpath))

        i = 1
        for f in self.settings:
            if not "test_name" in f.keys():
                raise InvalidConfigError(
                    "Test {0} in {1} must contain mandatory field 'test_name', specifying the (unique) name of the test".format(i, self.relpath))

            test_types = [value for value in f.keys() if value in self.valid_test_types]
            if len(test_types) > 1:
                raise InvalidConfigError(
                    "Test {0} in {1} must specify only one test type ('flags', 'command' or 'verification')".format(i, self.relpath))


            # Check each test type is valid
            if "flags" in f.keys():
                if not "files" in f.keys():
                    raise InvalidConfigError(
                        "Test {0} in {1} must contain mandatory field 'files', specifying test files".format(i, self.relpath))

                if len(f["files"]) == 0:
                    raise InvalidConfigError(
                        "Test {0} in {1} must have at least 1 test file".format(i, self.relpath))
                if len(f["flags"]) == 0:
                    raise InvalidConfigError(
                        "Test {0} in {1} must have at least 1 compiler flag".format(i, self.relpath))

                for flag in f["flags"]:
                    if re.compile(r'^\s*--dist-dir').match(flag):
                        raise InvalidConfigError(
                            "The use of the '--dist-dir' flag is prohibited in test flags (test {}, in {})".format(i, self.relpath))
            elif "command" in f.keys():
                if "files" in f:
                    raise InvalidConfigError(
                        "Test {0} in {1} cannot specify field 'files' for 'command' test type".format(i, self.relpath))
            elif "verification" in f.keys():
                raise InvalidConfigError(
                    "Test {0} in {1}: 'verification' field currently not supported".format(i, self.relpath))
            else:
                raise InvalidConfigError(
                    "Test {0} in {1} must specify a test type ('flags', 'command' or 'verification')".format(i, self.relpath))


            # Check expected result
            if not "expected_result" in f.keys():
                raise InvalidConfigError(
                    "Test {0} in {1} must contain mandatory field 'expected_result'".format(i, self.relpath))
            if f["expected_result"] not in ["error", "pass", "fail", "wip"]:
                raise InvalidConfigError("""Field 'expected_result' must be one of 'pass', 'fail', 'error' or 'wip' in test {0} in {1}.\n Actual value: '{2}'"""
                                         .format(i, self.relpath, str(f["expected_result"])))

            for k in f.keys():
                if (k not in self.valid_test_fields) and (k not in self.valid_test_types):
                    raise InvalidConfigError(
                        "Field '{0}' not a valid field in test {1} in {2}".format(k, i, self.relpath))

            i += 1

    def get_all_test_names(self):
        return [x['test_name'] for x in self.settings ]


    # Run the cogent compiler with the given flags, under test schema test_info
    def run_cogent(self, filename, flags, test_info):
        fname = os.path.join(self.dir, filename)
        # Check file exists and error gracefully
        if not os.path.exists(fname):
            def f(): return ("error", "Source file '{}' not found\n".format(
                fname), test_info['expected_result'])
            return TestResult(f(), fname, test_info['test_name'])

        # function that runs our test
        def test():
            setup_dist()

            res = subprocess.run(["cogent"] + flags + ["--dist-dir={}".format(TEST_DIST_DIR)] + [fname],
                                 stderr=subprocess.STDOUT,
                                 stdout=subprocess.PIPE,
                                 cwd=self.dir)

            status = "pass"

            # The compiler returns an error code
            if res.returncode == 134:
                status = "fail"
            # The haskell process crashes/errors
            elif res.returncode != 0:
                status = "error"

            return (status, res.stdout.decode("utf-8"), test_info["expected_result"])

        return TestResult(test(), fname, test_info['test_name'])

    # Runs a shell command
    def run_command(self, test_info):
        command = test_info['command']

        def test():
            res = subprocess.run(command,
                                 stderr=subprocess.STDOUT,
                                 stdout=subprocess.PIPE,
                                 cwd=self.dir,
                                 shell=True)
            
            status = "pass"
            if res.returncode == 1:
                status = "fail"
            if res.returncode == 2:
                status = "error"

            return (status, res.stdout.decode("utf-8"), test_info["expected_result"])
        
        return TestResult(test(), test_info['test_name'], test_info['test_name'])


    def print_test_header(self, test_name):
        print("-" * self.header_block_len,
              " {} ".format(test_name),
              "-" * self.header_block_len)

    # dispatches a test according to its type
    def run_test(self, test):
        results = []
        if "flags" in test.keys():
            for f in test['files']:
                results.append(self.run_cogent(f, test['flags'], test))
        elif "command" in test.keys():
            results.append(self.run_command(test))
        elif "verification" in test.keys():
            # This should error
            pass
        else:
            # Should be impossible
            pass
        return results

    # Run one test by name
    def run_one(self, test_name):
        results = []
        for test in self.settings:
            if test_name == test['test_name']:
                self.print_test_header(test_name)
                results += self.run_test(test)
                print()
                break
        return results

    # Run all tests in the configuration file
    def run_all(self):
        results = []
        for test in self.settings:
            self.print_test_header(test['test_name'])
            results += self.run_test(test)
            print()
        return results


# Based on an asbolute path for a test file, get it's configuration
def get_cfg_from_test_name(f):
    cfgs = get_configs()
    for c in cfgs:
        if f in c.get_all_test_names():
            return c
    return None


# Finds and runs a list of tests
def run_tests(test_names):
    res = []
    for name in test_names:
        conf = get_cfg_from_test_name(name)
        if conf is None:
            print(colored("Cannot find config file containing test name {}".format(name), "red"))
            sys.exit(1)
        res += conf.run_one(name)
    return res

# Find all configuration files in the test directory
def get_configs_with_errors():
    files = Path(".").rglob(CONFIG_FILE_NAME)
    files = [os.path.abspath(x) for x in files]
    cfgs = []
    errored = False
    for x in files:
        xname = os.path.relpath(x)
        try:
            cfgs.append(TestConfiguration(x))
        except InvalidConfigError as e:
            print(colored("Config error: ", "red"), e)
            errored = True
        except ScannerError as e:
            print(colored("Error", "red"), "- syntax error in test file {}".format(xname))
            errored = True
        except OSError as err:
            print(colored("Error", "red"), "- could not find config file for test file {}".format(xname))
            errored = True
    return (cfgs, errored)

# Finds all configuration files, ignoring errors
def get_configs():
    cfgs, _ = get_configs_with_errors()
    return cfgs

# Checks if all configuration files are valid
def validate():
    # Will implicitly run the configuration check
    cfgs, err = get_configs_with_errors()
    if err:
        return err

    names = []
    for c in cfgs:
        names += [(x, c.relpath) for x in c.get_all_test_names()]
    
    # Validates that each test name features only once
    seen_names = set()
    for (n,f) in names:
        same = list(filter(lambda x: x[0] == n, names))
        if len(same) > 1 and n not in seen_names:
            err = True
            print(colored("Test name '{}' used multiple times:".format(n), "red"))
            seen_files = set()
            for (x,y) in same:
                if y in seen_files: continue
                samefile = list(filter(lambda z: z[1] == y, names))
                print("Seen {1} time(s) in {2}".format(
                    x,
                    len(samefile) - len(set(samefile)) + 1,
                    y
                ))
                seen_files.add(y)
        seen_names.add(n)
    return err


if __name__ == "__main__":
    # Check if cogent is installed
    cogent = shutil.which("cogent")
    if cogent is None:
        print("Could not find cogent compiler on PATH - Please install cogent and place it on the PATH")
        sys.exit(1)

    ap = argparse.ArgumentParser(
        description="Cogent Testing Framework",
        epilog="Test configurations must be stored in a '{}' file".format(
            CONFIG_FILE_NAME),
        allow_abbrev=False
    )
    ap.add_argument(dest="only_test",
                    type=str,
                    help="only run specified tests", 
                    metavar="TEST_NAME",
                    nargs='*')
    ap.add_argument("--verbose", "-v", 
                    dest="verbose",
                    help="print output for given tests even if they pass (none supplied = all tests)",
                    metavar="TEST_NAME",
                    nargs='*')
    ap.add_argument("--validate", "-t", 
                    dest="validate",
                    action="store_true",
                    help="Check the format of all config files is correct")

    args = ap.parse_args()

    # Validate all config files
    err = validate()
    if args.validate:
        if not err:
            print(colored("All configuration files okay!", "green"))
        else:
            print(colored("Errors found in above configuration files", "red"))
        sys.exit((1 if err else 0))
    if err:
        sys.exit(1)

    configs = []
    if args.verbose is not None:
        verbose_test_names = args.verbose

    # clean the dist dir
    setup_dist()

    results = []
    # If we're only running specific tests
    if args.only_test != []:
        results = run_tests(args.only_test)
    # Otherwise, run all possible tests
    else:
        configs = get_configs()
        for c in configs:
            results += c.run_all()

    final_results = []

    errs   = 0
    passes = 0
    fails  = 0
    wips   = 0

    for res in results:
        (status, _, expected) = res.test

        p = res.result()
        final_results.append(p or expected == "wip")

        if expected == "wip":
            wips += 1
        elif not p and status == "error":
            errs += 1
        elif p:
            passes += 1
        else:
            fails += 1
    
    print("-"*20 + " Final results: " + "-" * 20)
    print()

    print("{:>20}{:>20}".format("Result", "Amount"))
    print("{:>20}{:>20}".format("Errors", errs))
    print("{:>20}{:>20}".format("Passes", passes))
    print("{:>20}{:>20}".format("Fails", fails))
    print("{:>20}{:>20}".format("Work In Progress", wips))
    print()

    if not all(final_results):
        sys.exit(1)