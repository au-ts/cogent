#!/usr/bin/env python3

import os, subprocess, sys, importlib, re, shutil, argparse
from collections import OrderedDict
from pathlib import Path

# Check version is at least python 3.7
if sys.version_info[0] < 3:
    print(">= python 3.6 is required to run the testing script")
    print("Your version: {0}.{1}.{2}".format(sys.version_info[0], sys.version_info[1], sys.version_info[2]))
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

from ruamel.yaml import YAML
from termcolor import colored

CONFIG_FILE_NAME = "config.yaml"
TEST_DIST_DIR = os.path.join(os.path.dirname(os.path.realpath(__file__)), "dist")

def clean_dist():
    # rm -rf
    shutil.rmtree(TEST_DIST_DIR, ignore_errors=True)

def setup_dist():
    if os.path.exists(TEST_DIST_DIR):
        clean_dist()
    os.mkdir(TEST_DIST_DIR)

# Represents the result of a test
# Takes in a function which returns
#   (status, errormsg, expected)
# where status, expected :: "pass" | "fail" | "error" | "wip"
class TestResult: 

    block_len = 15

    def __init__(self, name, test, fullname):
        self.name = name
        self.test = test
        self.fullname = fullname

    # Printing test results
    def display(self, is_verbose):
        acc = ""
        print("{}: ".format(os.path.relpath(self.fullname)), end="")
        (status, output, expected) = self.test()

        if expected == "wip":
            acc += colored("WIP (Pass by defualt)\n", "green")
            if is_verbose:
                acc += ("=" * self.block_len + "Test Output" + "=" * self.block_len) + "\n"
                acc += output
                acc += ("=" * self.block_len + len("Test Output") * "=" + "=" * self.block_len) + "\n"
            print(acc, end="")
            return True

        if status == "error" and expected != "error":
            acc += colored("Error? ", "yellow") + "Reason:\n" + output + "\n"
        elif status == expected:
            if status == "pass":
                acc += colored("Passed\n", "green")
            elif status == "fail":
                acc += colored("Failed (as expected)\n", "green")
            elif status == "error":
                acc += colored("Error (as expected)\n", "green")
            if is_verbose:
                acc += ("=" * self.block_len + "Test Output" + "=" * self.block_len) + "\n"
                acc += output
                acc += ("=" * self.block_len + len("Test Output") * "=" + "=" * self.block_len) + "\n"
        else:
            if expected == "error":
                acc += coloured("Test ran but was expected to error", "red")
            elif expected == "pass":
                acc += colored("Failed", "red") + "\n" 
            elif expected == "fail":
                acc += colored("Failed (expected fail, got pass)", "red") + "\n" 

            acc += ("=" * self.block_len + "Test Output" + "=" * self.block_len) + "\n"
            acc += output
            acc += ("=" * self.block_len + len("Test Output") * "=" + "=" * self.block_len) + "\n"

        print(acc, end="")
        return status == expected

# For validating configurations
class InvalidConfigError(Exception):
    pass

# Represents a test configuration file
# Can perform multiple actions according to the layout of the file
class TestConfiguration:

    valid_test_fields = ["files", "flags", "expected_result"]

    # file path must be ABSOLUTE
    def __init__(self, filepath):
        with open(filepath, 'r') as f:
            self.settings = YAML().load(f.read())
            self.filepath = filepath
            self.dir = os.path.dirname(filepath)
            self.validate_config()
    
    # Checks a given config file is valid
    def validate_config(self):
        relpath = os.path.relpath(self.filepath)
        if (not isinstance(self.settings, OrderedDict)) or (not "test" in self.settings.keys()):
            raise InvalidConfigError("{}: Config files must start with a single 'test' field at the top level".format(self.filepath))
        if not isinstance(self.settings["test"], list):
            raise InvalidConfigError("Top level test field must contain a list of test entries")

        i = 1
        for f in self.settings["test"]:
            if not "files" in f.keys():
                raise InvalidConfigError("Test {0} in {1} must contain mandatory field 'files'".format(i, relpath))
            if not "flags" in f.keys():
                raise InvalidConfigError("Test {0} in {1} must contain mandatory field 'flags'".format(i, relpath))
            if not "expected_result" in f.keys():
                raise InvalidConfigError("Test {0} in {1} must contain mandatory field 'expected_result'".format(i, relpath))

            if len(f["files"]) == 0:
                raise InvalidConfigError("Test {0} in {1} must have at least 1 test file".format(i, relpath))
            if len(f["flags"]) == 0:
                raise InvalidConfigError("Test {0} in {1} must have at least 1 compiler flag".format(i, relpath))
            if f["expected_result"] not in ["error", "pass", "fail", "wip"]:
                raise InvalidConfigError("""Field 'expected_result' must be one of 'pass', 'fail', 'error' or 'wip' in test {0} in {1}\n. Actual value: {2}"""
                                            .format(i, relpath, str(f["expected_result"])))

            for k in f.keys():
                if k not in self.valid_test_fields:
                    raise InvalidConfigError("Field '{0}' not a valid field in test {1} in {2}".format(k, i, relpath))

            for flag in f["flags"]:
                if re.compile(r'^\s*--dist-dir').match(flag):
                    raise InvalidConfigError("The use of the '--dist-dir' flag is prohibited in test flags (test {}, in {})".format(i, relpath))


            i += 1

    # Run the cogent compiler with the given flags, under test schema d
    def run_cogent(self, name, flags, d):
        fname = os.path.join(self.dir, name)
        # Check file exists and error gracefully
        if not os.path.exists(fname):
            f = lambda: ("error", "Source file '{}' not found".format(fname), d['expected_result'])
            return TestResult(name, f, fname)

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

            return (status, res.stdout.decode("utf-8"), d["expected_result"])

        return TestResult(name, test, fname)

    # Run one test by name
    def run_one(self, test_name):
        results = []
        for test in self.settings['test']:
            if test_name in test['files']:
                results.append(self.run_cogent(test_name, test['flags'], test))
        return results

    # Run all tests in the configuration file
    def run_all(self):
        results = []
        for test in self.settings['test']:
            for f in test['files']:
                results.append(self.run_cogent(f, test['flags'], test))
        return results


# Based on an asbolute path for a test file, get it's configuration
def get_cfg_from_test_file(f):
    return os.path.join(os.path.dirname(os.path.realpath(f)), CONFIG_FILE_NAME)


# Run tests for each provided test
def run_tests(files):
    results = []
    for f in files:
        try:
            conf = TestConfiguration(get_cfg_from_test_file(f))
            name = os.path.basename(f)
            res = conf.run_one(name)
            results += res
        except InvalidConfigError as e:
            print(colored("Config error: ", "red"), e)
        except OSError:
            print("error - could not find config file for test file {}".format(f))
    
    return results

# Find all configuration files in the test directory
def get_configs():
    files = Path(".").rglob(CONFIG_FILE_NAME)
    files = [os.path.abspath(x) for x in files]
    cfgs = []
    for x in files:
        try:
            cfgs.append(TestConfiguration(x))
        except InvalidConfigError as e:
            print(colored("Config error: ", "red"), e)
        except OSError as err:
            print("error - could not find config file for test file {}".format(x))
            sys.exit(1)
    return cfgs


if __name__ == "__main__":

    # Check if cogent is installed
    cogent = shutil.which("cogent")
    if cogent is None:
        print("Could not find cogent compiler on PATH - Please install cogent and place it on the PATH")
        sys.exit(1)

    ap = argparse.ArgumentParser(
            description="Cogent Testing Framework",
            epilog="Test configurations must be stored in a '{}' file".format(CONFIG_FILE_NAME)
            )
    ap.add_argument("--only", dest="only_test", help="only run specified tests", metavar="FILE.cogent", nargs='+')
    ap.add_argument("--verbose",   dest="verbose",   help="print output for given tests even if they pass (none supplied = all tests)",
                                   metavar="FILE.cogent", nargs='*')

    args = ap.parse_args()
    
    configs = []
    verbose = None
    if args.verbose is not None:
        verbose = [os.path.join(os.path.abspath("."), v) for v in args.verbose]

    results = []
    # If we're only running specific tests
    if args.only_test is not None:
        results = run_tests(args.only_test)
    # Otherwise, run all possible tests
    else:
        configs = get_configs()
        for c in configs:
            for res in c.run_all():
                results.append(res)

    all_passed = True

    final_results = []

    setup_dist()

    for res in results:
        p = res.display(verbose is not None and (verbose == [] or res.fullname in verbose))
        final_results.append(p)
    
    if not all(final_results):
        sys.exit(1)
