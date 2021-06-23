#!/usr/bin/env python3

from termcolor import colored
from ruamel.yaml import YAML
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
        print("Dependency module '{}' not installed - please install via pip3".format(name))
        return False


importok = [check_import("ruamel.yaml"), check_import("termcolor")]

if not all(importok):
    sys.exit(1)

#
# Script Starts here
#

class PreconditionViolation(Exception):
    pass


CONFIG_FILE_NAME = "config.yaml"
TEST_SCRIPT_DIR = os.path.dirname(os.path.realpath(__file__))
TEST_DIST_DIR = Path(TEST_SCRIPT_DIR, "dist")

def clean_dist():
    # rm -rf
    shutil.rmtree(TEST_DIST_DIR, ignore_errors=True)


def setup_dist():
    if os.path.exists(TEST_DIST_DIR):
        clean_dist()
    os.mkdir(TEST_DIST_DIR)


# A global list of test names that should be verbose
# if it is empty, then verbose is off
# if it is None, that means all tests should be verbose
# if it is nonempty, only the test names inside should be verbose
verbose_test_names = []

# all possible results of a test
valid_results = ["error", "pass", "fail", "wip", "wip-pass", "wip-fail"]

# Represents the result of a test
# Takes in a function which returns
#   (status, errormsg, expected)
# where status, expected :: "pass" | "fail" | "error" | "wip-pass" | "wip-fail" | "wip"

def is_wip(expected):
    return (expected == "wip" or
            expected == "wip-pass" or
            expected == "wip-fail")

class TestContext:
    def __init__(self, repo, cogent, dist_dir, script_dir, phases, ignore_phases):
        self.repo = repo
        self.cogent = cogent
        self.dist_dir = dist_dir
        self.script_dir = script_dir
        self.phases = phases
        self.ignore_phases = ignore_phases

class Phase:
    def __init__(self, phase_path):
        self.name = phase_path.stem
        self.phase_file = phase_path.resolve()

    def run(self, context, fname, test):
        return subprocess.run([self.phase_file] + [fname],
                                stderr = subprocess.STDOUT,
                                stdout = subprocess.PIPE,
                                cwd = context.script_dir,
                                env = { "COGENT_REPO": context.repo
                                      , "TEST_DIST_DIR": context.dist_dir
                                      , "HOME": os.environ['HOME']
                                      })

class TestResult:

    block_len = 15

    def __init__(self, test, fullname, test_name):
        self.test = test
        self.fullname = fullname
        self.test_name = test_name
        self.display()

    def result(self):
        (status, _, expected) = self.test
        return status == expected or is_wip(expected)

    # Printing test results
    def display(self):

        acc = ""
        print("{}: ".format(os.path.relpath(self.fullname)), end="")
        (status, output, expected) = self.test

        be_verbose = (verbose_test_names is None or
                      self.test_name in verbose_test_names)


        if expected == "wip-pass":
            if status == "pass":
                acc += colored("WIP (Passed as expected)\n", "green")
            else:
                acc += colored("WIP (expected pass, got " + status + ")\n", "yellow")
        elif expected == "wip-fail":
            if status == "fail":
                acc += colored("WIP (Failed as expected)\n", "green")
            else:
                acc += colored("WIP (expected fail, got " + status + ")\n", "yellow")

        elif expected == "wip":
            acc += colored("WIP (got " + status + ")\n", "yellow")

        elif status == "error" and expected != "error":
            acc += colored("Error? ", "yellow") + "\nReason:\n"
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

    valid_test_fields = ["files", "expected_result", "test_name", "flags", "phase", "run"]

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

        i = 1  # the number id of the test

        for f in self.settings:
            # all keys must be valid keys
            for k in f.keys():
                if k not in self.valid_test_fields:
                    raise InvalidConfigError(
                        "Field '{0}' not a valid field in test {1} in {2}".format(k, i, self.relpath))

            # no mandatory keys are missing
            if not "test_name" in f.keys():
                raise InvalidConfigError(
                    "Test {0} in {1} must contain mandatory field 'test_name', specifying the (unique) name of the test".format(i, self.relpath))

            if not "files" in f.keys():
                raise InvalidConfigError(
                    "Test {0} in {1} must contain mandatory field 'files', a list with at least 1 test".format(i, self.relpath))
            if len(f["files"]) == 0:
                raise InvalidConfigError(
                    "Test {0} in {1} must have at least 1 test file".format(i, self.relpath))

            if not "expected_result" in f.keys():
                raise InvalidConfigError(
                    "Test {0} in {1} must contain mandatory field 'expected_result'".format(i, self.relpath))
            if f["expected_result"] not in valid_results:
                raise InvalidConfigError("""Field 'expected_result' must be one of {0} in test {1} in {2}\n. Actual value: {3}"""
                                         .format(valid_results, i, self.relpath, str(f["expected_result"])))

            # only one of "flags", "phase", "run" can appear.
            if "flags" in f:
                if len(f["flags"]) == 0:
                    raise InvalidConfigError(
                        "Test {0} in {1} must have at least 1 compiler flag".format(i, self.relpath))
                if "phase" in f or "run" in f:
                    raise InvalidConfigError(
                        "Test {0} in {1} can only have one of 'flags', 'phase' or 'run' scheme".format(i, self.relpath))

                for flag in f["flags"]:
                    if re.compile(r'^\s*--dist-dir').match(flag):
                        raise InvalidConfigError(
                            "The use of the '--dist-dir' flag is prohibited in test flags (test {}, in {})".format(i, self.relpath))

            elif "phase" in f:
                pass # the checks are performed when the phase is run
            elif "run" in f:
                pass # no checks are performed
            else:
                raise InvalidConfigError(
                    "Test {0} in {1} doesn't have any test scheme specified".format(i, self.relpath))

            i += 1

    def get_all_test_names(self):
        return [x['test_name'] for x in self.settings ]

class Test:
    def __init__(self, testConfig):
        self.config = testConfig

    # Run the cogent compiler with the given flags, under test schema
    def run_cogent(self, context, filename, test_info):
        fname = os.path.join(self.config.dir, filename)
        # Check file exists and error gracefully
        if not os.path.exists(fname):
            return TestResult(
                        ("error", "Source file '{}' not found".format(fname), test_info['expected_result']),
                        fname,
                        test_info['test_name']
                    )

        # run our test
        setup_dist()

        # flags must exist
        flags = test_info['flags']

        res = subprocess.run([context.cogent] + flags + ["--dist-dir={}".format(TEST_DIST_DIR)] + [fname],
                                stderr=subprocess.STDOUT,
                                stdout=subprocess.PIPE,
                                cwd=self.config.dir)

        status = "pass"

        # The compiler returns an error code
        if res.returncode == 134:
            status = "fail"
        # The haskell process crashes/errors
        elif res.returncode != 0:
            status = "error"

        result = (status, res.stdout.decode("utf-8"), test_info["expected_result"])

        return TestResult(result, fname, test_info['test_name'])

    # Run a specific phase, according to the phase config file.
    def run_phase(self, context, filename, phase, test_info):
        fname = os.path.join(self.config.dir, filename)
        # Check file exists and error gracefully
        if not os.path.exists(fname):
            return TestResult(
                        ("error", "Source file '{}' not found".format(fname), test_info['expected_result']),
                        fname,
                        test_info['test_name']
                    )

        if not context.repo:
            return TestResult(
                        ("error", "repo not found", test_info['expected_result']),
                        fname,
                        test_info['test_name']
                    )

        # runs the test
        setup_dist()

        res = phase.run(context, fname, test_info)

        status = "pass"

        # The compiler returns an error code
        if res.returncode == 134:
            status = "fail"
        # The haskell process crashes/errors
        elif res.returncode != 0:
            status = "error"

        result = (status, res.stdout.decode("utf-8"), test_info["expected_result"])

        return TestResult(result, fname, test_info['test_name'])

    # Run shell commands as specified
    def run_cmds(self, context, filename, test_info):
        fname = os.path.join(self.config.dir, filename)
        cmds = test_info['run']

        if os.path.isdir(fname):
            test_dir = fname
        else:
            test_dir = self.config.dir

        # run the commands
        status = "pass"
        output = []
        for cmd in cmds:
            cmd_res = subprocess.run(cmd.split(), 
                                     cwd = test_dir,
                                     stderr = subprocess.STDOUT,
                                     stdout = subprocess.PIPE)
            if cmd_res.returncode != 0:
                status = "fail"
                output.append(cmd_res.stdout.decode("utf-8"))
                break
        result = (status, "\n".join(output), test_info["expected_result"])

        return TestResult(result, fname, test_info['test_name'])

    def print_test_header(self, test_name):
        print("-" * self.config.header_block_len,
              " {} ".format(test_name),
              "-" * self.config.header_block_len)

    # Run one test by name
    def run_one(self, context, test_name):
        return self.run_tests(context, filter(lambda t: test_name == t['test_name'], self.config.settings))

    # Run all tests in the configuration file
    def run_all(self, context):
        return self.run_tests(context, self.config.settings)

    def run_tests(self, context, tests):
        results = []
        for test in tests:
            self.print_test_header(test['test_name'])
            for f in test['files']:
                if "flags" in test and "cogent" not in context.ignore_phases:
                    results.append( self.run_cogent(context, f, test) )

                elif "phase" in test:
                    phasename = test['phase']
                    if phasename in context.ignore_phases or context.phases is None:
                        pass
                    else:
                        try:
                            results.append( self.run_phase(context, f, context.phases[phasename], test) )
                        except KeyError:
                            results.append( TestResult(
                                ("error", "phase not found: {}\n".format(phasename), test['expected_result']),
                                f,
                                test['test_name']
                            ))

                elif "run" in test:
                    results.append( self.run_cmds(context, f, test) )

                else:
                    pass
            print()
        return results

# a collection of configurations
class Configurations:
    def __init__(self, path):
        self.files = [f.resolve() for f in path.rglob(CONFIG_FILE_NAME)]
        self.configs = []
        self.errConfigs = []
        for f in self.files:
            try:
                self.configs.append(TestConfiguration(f))
            except InvalidConfigError as e:
                self.errConfigs.append(e)
            except OSError as e:
                self.errConfigs.append(e)

    def has_erroring_configs(self):
        return self.errConfigs != []

    def print_errs(self):
        print(self.errConfigs)
        for e in self.errConfigs:
            if type(e) is InvalidConfigError:
                print(colored("Config error: ", "red"), e)
            elif type(e) is OSError:
                print(colored("error - could not find config file for test file {}".format(e), "red"))

    # Based on an asbolute path for a test file, get it's configuration
    def get_cfg_from_test_name(self, f):
        cfgs = self.get_configs()
        for c in cfgs:
            if f in c.get_all_test_names():
                return c
        return None

    def get_configs(self):
        return self.configs



#
# Main script
#

def main():
    ap = argparse.ArgumentParser(
        description="Cogent Testing Framework",
        epilog="Test configurations must be stored in a '{}' file".format(
            CONFIG_FILE_NAME),
        allow_abbrev=False
    )
    ap.add_argument("--only", "-o", dest="only_test",
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
    ap.add_argument("--extra-phases", "-p",
                    dest="phase_dir",
                    default=None,
                    help="set the location of the additional phase directory")
    ap.add_argument("--ignore-phases",
                    dest="ignore_phases",
                    action="store",
                    nargs="+",
                    default=[],
                    help="ignore the tests for the specified phases")
    ap.add_argument("--repo",
                    dest="repo",
                    help="set the location of the repository root")
    ap.add_argument("--cogent",
                    dest="cogent",
                    default="cogent",
                    help="specify the location of the cogent compiler")
    ap.add_argument("--ignore-errors",
                    dest="ignore_errors",
                    action="store_true",
                    help="if enabled, a test error does not cause the script to exit with an error")
    args = ap.parse_args()

    cogent = shutil.which(args.cogent)

    if args.repo is not None:
      repo = os.path.abspath(args.repo)
    else:
      repo = None
      print("Warning: repository directory not set; use --repo")

    if args.phase_dir is not None:
      phase_dir = os.path.abspath(args.phase_dir)
    else:
      phase_dir = None

    # Check if cogent is installed
    if cogent is None:
        print("Could not find cogent compiler - Please either add it to your PATH or set --cogent")
        sys.exit(1)

    print("Using repository: " + str(repo))
    print("Using cogent: " + cogent)
    print("Using phase dir: " + str(phase_dir))

    if phase_dir is not None and Path(phase_dir).exists():
      files = Path(phase_dir).glob("*.sh")
      phases = dict(map(lambda p: (p.stem,Phase(p)), files))
    else:
      phases = None

    context = TestContext(repo, cogent, TEST_DIST_DIR, TEST_SCRIPT_DIR, phases, args.ignore_phases)

    # find all config files
    configs = Configurations(Path("."))

    # Validate all config files
    if args.validate:
        isErr = configs.has_erroring_configs()
        if isErr:
            configs.print_errs()
            print(colored("Errors found in above configuration files", "red"))
        else:
            print(colored("All configuration files okay!", "green"))
        sys.exit((1 if isErr else 0))
    elif configs.has_erroring_configs():
        print(colored("Errors found in above configuration files:", "red"))
        print(colored("  call with --validate for more info", "red"))
        sys.exit(1)

    if args.verbose is None:
        verbose_test_names = []
    elif not args.verbose:
        verbose_test_names = None  # every test will be verbose
    else:
        verbose_test_names = args.verbose

    results = []
    # If we're only running specific tests
    if args.only_test is not None:
        test_names = args.only_test
        for test_name in test_names:
            conf = configs.get_cfg_from_test_name(test_name)
            if conf is None:
                print(colored("Cannot find config file containing test name {}".format(test_name), "red"))
                sys.exit(1)
            test = Test(conf)
            results = test.run_one(context, test_name)
    # Otherwise, run all possible tests
    else:
        tests = list(map(lambda config: Test(config), configs.get_configs()))

        for test in tests:
            subresults = test.run_all(context)
            results.extend(subresults)

    setup_dist()

    errs   = 0
    passes = 0
    fails  = 0
    wips   = 0

    for res in results:
        (status, _, expected) = res.test

        if is_wip(expected):
            wips += 1
        elif status == "error":
            errs += 1
        elif res.result():
            passes += 1
        else:
            fails += 1
    
    print("-"*15 + " Final results: " + "-" * 15)
    print()

    print("{:>16}{:>16}".format("Result", "Amount"))
    print("{:>16}{:>16}".format("Errors", errs))
    print("{:>16}{:>16}".format("Passes", passes))
    print("{:>16}{:>16}".format("Fails", fails))
    print("{:>16}{:>16}".format("Work In Progress", wips))
    print()

    if fails != 0 or (not args.ignore_errors and errs != 0):
        sys.exit(1)


if __name__ == "__main__":
    main()

