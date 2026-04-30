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


ANSI_RE = re.compile(r"\x1b\[[0-?]*[ -/]*[@-~]")
TEST_RESULT_RE = re.compile(
    r"^\s*\d+/\d+\s+Test\s+#\d+:\s+(.*?)\s+\.+\*{3}(\S+)")
FAILED_HEADER = "The following tests FAILED:"
FAILED_ENTRY_RE = re.compile(r"^(\s*\d+\s+-\s+)(.*?)(\s+\(([^)]+)\)(.*))$")
TIMEOUT_OUTPUT_RE = re.compile(r"^(?:[>✖]\s*)?Timeout$")


class Color:
    RED = "\033[91m"
    ENDC = "\033[0m"


def strip_ansi(text):
    return ANSI_RE.sub("", text)


def red(text):
    return Color.RED + text + Color.ENDC


def is_timeout_output(line):
    return TIMEOUT_OUTPUT_RE.match(strip_ansi(line).strip()) is not None


def output_line(line):
    print(line, flush=True)


def print_failed_sections(entries, timed_out_tests, output):
    failed = []
    timed_out = []

    for line in entries:
        match = FAILED_ENTRY_RE.match(strip_ansi(line))
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
        output(FAILED_HEADER)
        for line in failed:
            output(line)

    if timed_out:
        if failed:
            output("")
        output(red("The following tests TIMED OUT:"))
        for line in timed_out:
            output(red(line))


class CTestOutputFilter:
    def __init__(self, output):
        self.output = output
        self.current_failed_test = None
        self.timed_out_tests = set()
        self.in_failed_section = False
        self.failed_entries = []

    def process_line(self, line):
        clean_line = strip_ansi(line)

        result_match = TEST_RESULT_RE.match(clean_line)
        if result_match:
            self.current_failed_test = result_match.group(1).rstrip()
            if result_match.group(2) == "Timeout":
                self.timed_out_tests.add(self.current_failed_test)

        if is_timeout_output(line) and self.current_failed_test is not None:
            self.timed_out_tests.add(self.current_failed_test)

        if self.in_failed_section:
            if FAILED_ENTRY_RE.match(clean_line):
                self.failed_entries.append(line)
                return

            self.flush_failed_section()

        if clean_line == FAILED_HEADER:
            self.in_failed_section = True
            return

        self.output(line)

    def flush_failed_section(self):
        print_failed_sections(
            self.failed_entries, self.timed_out_tests, self.output)
        self.in_failed_section = False
        self.failed_entries = []

    def finish(self):
        if self.in_failed_section:
            self.flush_failed_section()


def run_with_pipe(command):
    proc = subprocess.Popen(
        command,
        stderr=subprocess.STDOUT,
        stdout=subprocess.PIPE,
        text=True,
    )

    output_filter = CTestOutputFilter(output_line)
    try:
        for line in proc.stdout:
            output_filter.process_line(line.rstrip("\n"))
        return_code = proc.wait()
    except KeyboardInterrupt:
        proc.terminate()
        proc.wait()
        raise

    output_filter.finish()
    return return_code


def run_with_pty(command):
    import codecs
    import errno
    import os
    import pty

    master_fd, slave_fd = pty.openpty()
    proc = subprocess.Popen(
        command,
        stdin=subprocess.DEVNULL,
        stderr=slave_fd,
        stdout=slave_fd,
        close_fds=True,
    )
    os.close(slave_fd)

    output_filter = CTestOutputFilter(output_line)
    decoder = codecs.getincrementaldecoder(
        sys.stdout.encoding or "utf-8")("replace")
    pending = ""

    try:
        while True:
            try:
                chunk = os.read(master_fd, 4096)
            except OSError as err:
                if err.errno == errno.EIO:
                    break
                raise
            if not chunk:
                break
            pending += decoder.decode(chunk)
            while "\n" in pending:
                line, pending = pending.split("\n", 1)
                output_filter.process_line(line.rstrip("\r"))

        pending += decoder.decode(b"", final=True)
        if pending:
            output_filter.process_line(pending.rstrip("\r"))
        return_code = proc.wait()
    except KeyboardInterrupt:
        proc.terminate()
        proc.wait()
        raise
    finally:
        os.close(master_fd)

    output_filter.finish()
    return return_code


def main():
    command = sys.argv[1:]
    if command and command[0] == "--":
        command = command[1:]
    if not command:
        print("error: missing CTest command", file=sys.stderr)
        return 2

    if sys.stdout.isatty() and sys.platform != "win32":
        return run_with_pty(command)
    return run_with_pipe(command)


if __name__ == "__main__":
    sys.exit(main())
