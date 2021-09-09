#!/usr/bin/python
#
#
# Copyright 2014, NICTA
#
# This software may be distributed and modified according to the terms of
# the BSD 2-Clause license. Note that NO WARRANTY is provided.
# See "LICENSE_BSD2.txt" for details.
#
# @TAG(NICTA_BSD)
#
#
# Very simple command-line test runner.
#
# Ignores timeouts.
#

from __future__ import print_function

import argparse
import atexit
import datetime
import fnmatch
import memusage
import os
import signal
import subprocess
import sys
import testspec
import time
import traceback

# Try importing psutil.
PS_UTIL_AVAILABLE = False
try:
    import psutil
    from psutil import NoSuchProcess
    PS_UTIL_AVAILABLE = True
    if not hasattr(psutil.Process, "children") and hasattr(psutil.Process, "get_children"):
        psutil.Process.children = psutil.Process.get_children
except ImportError:
    pass

ANSI_RESET = "\033[0m"
ANSI_RED = "\033[31;1m"
ANSI_GREEN = "\033[32m"
ANSI_YELLOW = "\033[33m"
ANSI_WHITE = "\033[38m"
ANSI_BOLD = "\033[1m"

def output_color(color, s):
    """Wrap the given string in the given color."""
    if os.isatty(sys.stdout.fileno()):
        return color + s + ANSI_RESET
    return s

# Find a command in the PATH.
def which(file):
    for path in os.environ["PATH"].split(os.pathsep):
        candidate = os.path.join(path, file)
        if os.path.exists(candidate) and os.access(candidate, os.X_OK):
            return candidate
    return None

#
# Kill a process and all of its children.
#
# We attempt to handle races where a PID goes away while we
# are looking at it, but not where a PID has been reused.
#
def kill_family(parent_pid):
    if not PS_UTIL_AVAILABLE:
        return

    # Find process.
    try:
        process = psutil.Process(parent_pid)
    except NoSuchProcess:
        # Race. Nothing more to do.
        return

    # SIGSTOP everyone first.
    try:
        process.suspend()
    except NoSuchProcess:
        # Race. Nothing more to do.
        return
    process_list = [process]
    for child in process.children(recursive=True):
        try:
            child.suspend()
        except NoSuchProcess:
            # Race.
            pass
        else:
            process_list.append(child)


    # Now SIGKILL everyone.
    process_list.reverse()
    for p in process_list:
        p.send_signal(signal.SIGKILL)

#
# Run a single test.
#
# Return a tuple of (success, log, time_taken, memory_usage).
#
# Log only contains the output if verbose is *false*; otherwise, the
# log is output to stdout where we can't easily get to it.
#
def run_test(test, verbose=False):
    # Construct the base command.
    command = ["bash", "-c", test.command]

    # If we have a "pidspace" program, use that to ensure that programs
    # that double-fork can't continue running after the parent command
    # dies.
    if which("pidspace") != None:
        command = [which("pidspace"), "--"] + command

    # Print command and path.
    if verbose:
        print("\n")
        if os.path.abspath(test.cwd) != os.path.abspath(os.getcwd()):
            path = " [%s]" % os.path.relpath(test.cwd)
        else:
            path = ""
        print("    command: %s%s" % (test.command, path))

    output = subprocess.PIPE

    # Start timing.
    start_time = datetime.datetime.now()

    # Start the command.
    peak_mem_usage = None
    try:
        process = subprocess.Popen(command,
                stdout=output, stderr=subprocess.STDOUT, stdin=subprocess.PIPE,
                cwd=test.cwd, text=True)
        lines_iter = iter(process.stdout.readline, "")  # pytype: disable=attribute-error
        if verbose:
            for line in lines_iter:
                print(line, end='')
    except:
        output = "Exception while running test:\n\n%s" % (traceback.format_exc())
        atexit.register(lambda: kill_family(process.pid))
        if verbose:
            print(output)
        return (False, "ERROR", output, datetime.datetime.now() - start_time, peak_mem_usage)

    # If our program exits for some reason, attempt to kill the process.
    atexit.register(lambda: kill_family(process.pid))

    # Setup an alarm at the timeout.
    was_timeout = [False]
    def alarm_handler(sig, _):
        was_timeout[0] = True
        kill_family(process.pid)
    signal.signal(signal.SIGALRM, alarm_handler)
    signal.alarm(test.timeout)

    # Wait for the command to finish.
    with memusage.process_poller(process.pid) as m:
        (output, _) = process.communicate()
        peak_mem_usage = m.peak_mem_usage()

    # Cancel the alarm. Small race here (if the alarm fires just after the
    # process finished), but the returncode of our process should still be 0,
    # and hence we won't interpret the result as a timeout.
    signal.alarm(0)

    if output == None:
        output = ""
    if process.returncode == 0:
        status = "pass"
    elif was_timeout[0]:
        status = "TIMEOUT"
    else:
        status = "FAILED"
    return (process.returncode == 0, status, output, datetime.datetime.now() - start_time, peak_mem_usage)

def print_line(ch='-'):
    print("".join([ch for x in range(72)]))

# Print a status line.
def print_test_line_start(test_name, verbose=False):
    print("  running %-25s " % (test_name + " ..."), end="")
    sys.stdout.flush()

def print_test_line_end(test_name, color, status, time_taken, mem, verbose=False):
    if mem:
        # Report meory usage in gigabytes.
        mem = '%5.2fGB' % round(float(mem) / 1024 / 1024 / 1024, 2)
    if time_taken:
        # Strip milliseconds for better printing.
        time_taken = datetime.timedelta(seconds=int(time_taken.total_seconds()))
        time_taken = '%8s' % time_taken
    extras = ', '.join(filter(None, [time_taken, mem]))

    # Print status line.
    print(output_color(color, "%-10s" % status) + ('(%s)' % extras if extras else ''))
    if verbose:
        print("")
        print_line("=")
        print()
    sys.stdout.flush()

def print_test_line(test_name, color, status, time_taken, mem, verbose=False):
    print_test_line_start(test_name, verbose)
    print_test_line_end(test_name, color, status, time_taken, mem, verbose)

#
# Recursive glob
#
def rglob(base_dir, pattern):
    matches = []
    for root, dirnames, filenames in os.walk(base_dir):
        for filename in fnmatch.filter(filenames, pattern):
            matches.append(os.path.join(root, filename))
    return matches

#
# Exclusive rglob
#
def xrglob(base_dir, pattern, excl_dirs):
   matches = []
   if base_dir in excl_dirs: 
       return matches
   for root, dirnames, filenames in os.walk(base_dir):
       for excl_dir in excl_dirs:
           if root.startswith(os.path.abspath(excl_dir)): 
              break
       else:
           for filename in fnmatch.filter(filenames, pattern):
               matches.append(os.path.join(root, filename))
   return matches


#
# Run tests.
#
def main():
    # Parse arguments
    parser = argparse.ArgumentParser(description="Simple Regression Framework")
    parser.add_argument("-s", "--strict", action="store_true",
            help="be strict when parsing test XML files")
    parser.add_argument("-d", "--directory", action="store",
            metavar="DIR", help="directory to search for test files",
            default=os.getcwd())
    parser.add_argument("-x", "--exclude", action="append",
            metavar="DIR", help="directory to exclude while searching for test files (multiple -x can be given)",
            default=[])
    parser.add_argument("--brief", action="store_true",
            help="don't print failure logs at end of test run")
    parser.add_argument("-l", "--list", action="store_true",
            help="list known tests")
    parser.add_argument("--legacy", action="store_true",
            help="use legacy 'IsaMakefile' specs")
    parser.add_argument("-v", "--verbose", action="store_true",
            help="print test output")
    parser.add_argument("--limit", action="store",
            help="set line limit for logs", default=40)
    parser.add_argument("-t", "--transitive", action="store_true",
            help="also run dependencies transitively (only effective when TESTS specified)")
    parser.add_argument("tests", metavar="TESTS",
            help="tests to run (defaults to all tests)",
            nargs="*")
    args = parser.parse_args()

    # Search for test files:
    if not args.legacy:
        test_xml = sorted(xrglob(args.directory, "tests.xml", args.exclude))
        tests = testspec.parse_test_files(test_xml, strict=args.strict)
    else:
        # Fetch legacy tests.
        tests = testspec.legacy_testspec(args.directory)

    # Calculate which tests should be run.
    tests_to_run = []  # type: list[testspec.Test] 
    if len(args.tests) == 0:
        tests_to_run = tests
    else:
        desired_names = set(args.tests)  # type: set[str]
        bad_names = desired_names - set([t.name for t in tests])
        if len(bad_names) > 0:
            parser.error("Unknown test names: %s" % (", ".join(sorted(bad_names))))
        tests_to_run = [t for t in tests if t.name in desired_names]

    # Automatically include dependencies.
    if args.transitive:
        tests_to_run = testspec.add_deps(tests_to_run, tests)

    # List test names if requested.
    if args.list:
        for t in tests_to_run:
            print(t.name)
        sys.exit(0)

    # If running at least one test, and psutil is not available, print a warning.
    if len(tests_to_run) > 0 and not PS_UTIL_AVAILABLE:
        print("\n"
              "Warning: 'psutil' module not available. Processes may not be correctly\n"
              "stopped. Run\n"
              "\n"
              "    pip install --user psutil\n"
              "\n"
              "to install.\n"
              "\n")

    # Run the tests.
    print("Running %d test(s)...\n" % len(tests_to_run))
    failed_tests = set()  #type: set[testspec.Test]
    failed_test_log = []
    for t in tests_to_run:
        if len(t.depends & failed_tests) > 0:  # tests that are in both
            print_test_line(t.name, ANSI_YELLOW, "skipped", None, None)
            failed_tests.add(t.name)
            continue

        # Run the test.
        print_test_line_start(t.name, verbose=args.verbose)
        (passed, status, log, time_taken, mem) = run_test(t, verbose=args.verbose)

        # Print result.
        if not passed:
            failed_tests.add(t.name)
            failed_test_log.append((t.name, log, time_taken))
            print_test_line_end(t.name, ANSI_RED, "%s *" % status, time_taken, mem, verbose=args.verbose)
        else:
            print_test_line_end(t.name, ANSI_GREEN, status, time_taken, mem, verbose=args.verbose)

    # Print failure summaries unless requested not to.
    if not args.brief and len(failed_test_log) > 0:
        print("")
        log_limit = int(args.limit)
        for (failed_test, log, _) in failed_test_log:
            print_line()
            print("TEST FAILURE: %s" % failed_test)
            print("")
            log = log.rstrip("\n") + "\n"
            lines = log.split("\n")
            if len(lines) > 2 * log_limit:
                lines = lines[:log_limit] + ["..."] + lines[-log_limit:]
            print("\n".join(lines))
        print_line()

    # Print summary.
    print(("\n\n"
            + output_color(ANSI_WHITE, "%d/%d tests succeeded.") + "\n")
            % (len(tests_to_run) - len(failed_tests), len(tests_to_run)))
    if len(failed_tests) > 0:
        print(output_color(ANSI_RED, "Tests failed.") + "\n")
        sys.exit(1)
    else:
        print(output_color(ANSI_GREEN, "All tests passed.") + "\n")
        sys.exit(0)


if __name__ == "__main__":
    main()


