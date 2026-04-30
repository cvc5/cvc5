#!/usr/bin/env python3
###############################################################################
# This file is part of the cvc5 project.
#
# Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
# in the top-level source directory and their institutional affiliations.
# All rights reserved.  See the file COPYING in the top-level source
# directory for licensing information.
# #############################################################################
##
"""
Runs CTest and separates regression timeouts in CTest's final failure list.
"""

import re
import subprocess
import sys


TEST_RESULT_RE = re.compile(
    r"^\s*\d+/\d+\s+Test\s+#\d+:\s+(.*?)\s+\.+\*{3}(\S+)")
FAILED_HEADER = "The following tests FAILED:"
FAILED_ENTRY_RE = re.compile(r"^(\s*\d+\s+-\s+)(.*?)(\s+\(([^)]+)\)(.*))$")
TIMEOUT_RESULT = "CVC5_REGRESSION_RESULT: TIMEOUT"


def print_failed_sections(entries, timed_out_tests):
    failed = []
    timed_out = []

    for line in entries:
        match = FAILED_ENTRY_RE.match(line)
        if match is None:
            failed.append(line)
            continue

        test_name = match.group(2).rstrip()
        status = match.group(4)
        if status == "Timeout" or test_name in timed_out_tests:
            line = "{}{}{}{}{}".format(
                match.group(1),
                test_name,
                " " * (len(match.group(2)) - len(test_name)),
                " (Timeout)",
                match.group(5),
            )
            timed_out.append(line)
        else:
            failed.append(line)

    if failed:
        print(FAILED_HEADER)
        for line in failed:
            print(line)

    if timed_out:
        if failed:
            print()
        print("The following tests TIMED OUT:")
        for line in timed_out:
            print(line)


def main():
    command = sys.argv[1:]
    if command and command[0] == "--":
        command = command[1:]
    if not command:
        print("error: missing CTest command", file=sys.stderr)
        return 2

    proc = subprocess.Popen(
        command,
        stderr=subprocess.STDOUT,
        stdout=subprocess.PIPE,
        text=True,
    )

    current_failed_test = None
    timed_out_tests = set()
    in_failed_section = False
    failed_entries = []

    try:
        for line in proc.stdout:
            line = line.rstrip("\n")

            result_match = TEST_RESULT_RE.match(line)
            if result_match:
                current_failed_test = result_match.group(1).rstrip()
                if result_match.group(2) == "Timeout":
                    timed_out_tests.add(current_failed_test)

            if TIMEOUT_RESULT in line and current_failed_test is not None:
                timed_out_tests.add(current_failed_test)

            if in_failed_section:
                if FAILED_ENTRY_RE.match(line):
                    failed_entries.append(line)
                    continue

                print_failed_sections(failed_entries, timed_out_tests)
                in_failed_section = False
                failed_entries = []

            if line == FAILED_HEADER:
                in_failed_section = True
                continue

            print(line)

        return_code = proc.wait()
    except KeyboardInterrupt:
        proc.terminate()
        proc.wait()
        raise

    if in_failed_section:
        print_failed_sections(failed_entries, timed_out_tests)

    return return_code


if __name__ == "__main__":
    sys.exit(main())
