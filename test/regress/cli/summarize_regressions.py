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
Runs CTest and appends a compact regression failure summary.
"""

import argparse
import collections
import re
import subprocess
import sys


RESULT_RE = re.compile(r"^CVC5_REGRESSION_RESULT:\s+([A-Z_]+)\s*$")
FAILED_COUNT_RE = re.compile(r"\b(\d+) tests failed out of \d+")
FAILED_TEST_RE = re.compile(r"^\s*\d+\s+-\s+.*\(([^)]+)\)\s*$")


def pluralize(count, singular, plural):
    return singular if count == 1 else plural


def summarize(output):
    """Returns a one-line summary for failed regression tests, if available."""

    results = collections.Counter()
    ctest_timeouts = 0
    failed_total = None

    for line in output.splitlines():
        result_match = RESULT_RE.match(line)
        if result_match:
            results[result_match.group(1)] += 1
            continue

        failed_count_match = FAILED_COUNT_RE.search(line)
        if failed_count_match:
            failed_total = int(failed_count_match.group(1))
            continue

        failed_test_match = FAILED_TEST_RE.match(line)
        if failed_test_match and failed_test_match.group(1) == "Timeout":
            ctest_timeouts += 1

    timeouts = results["TIMEOUT"] + ctest_timeouts
    errors = results["FAILURE"]
    classified = timeouts + errors

    if failed_total is not None:
        errors += max(0, failed_total - classified)
        total = failed_total
    else:
        total = classified

    if total == 0:
        return None

    return (
        "Regression failure summary: {} {}, {} {}, {} {}.".format(
            total,
            pluralize(total, "failure", "failures"),
            errors,
            pluralize(errors, "error", "errors"),
            timeouts,
            pluralize(timeouts, "timeout", "timeouts"),
        )
    )


def main():
    parser = argparse.ArgumentParser(
        description="Runs CTest and summarizes regression failures.")
    parser.add_argument("command", nargs=argparse.REMAINDER)
    args = parser.parse_args()

    command = args.command
    if command and command[0] == "--":
        command = command[1:]
    if not command:
        parser.error("missing CTest command")

    proc = subprocess.Popen(
        command,
        stderr=subprocess.STDOUT,
        stdout=subprocess.PIPE,
        text=True,
    )

    output_lines = []
    try:
        for line in proc.stdout:
            output_lines.append(line)
            print(line, end="")
        return_code = proc.wait()
    except KeyboardInterrupt:
        proc.terminate()
        proc.wait()
        raise

    summary = summarize("".join(output_lines))
    if summary is not None:
        print()
        print(summary)

    return return_code


if __name__ == "__main__":
    sys.exit(main())
