#!/usr/bin/env python3
###############################################################################
# Top contributors (to current version):
#   Andres Noetzli, Mathias Preiner, Yoni Zohar
#
# This file is part of the cvc5 project.
#
# Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
# in the top-level source directory and their institutional affiliations.
# All rights reserved.  See the file COPYING in the top-level source
# directory for licensing information.
# #############################################################################
##
"""
Runs benchmark and checks for correct exit status and output.
"""

import argparse
import collections
import difflib
import os
import re
import shlex
import subprocess
import sys
import tempfile
import threading

g_args = None


class Color:
    BLUE = "\033[94m"
    GREEN = "\033[92m"
    YELLOW = "\033[93m"
    RED = "\033[91m"
    ENDC = "\033[0m"


class Tester:
    def __init__(self):
        pass

    def applies(self, benchmark_info):
        return True

    def run(self, benchmark_info):
        exit_code = EXIT_OK
        output, error, exit_status = run_benchmark(benchmark_info)
        if exit_status == STATUS_TIMEOUT:
            exit_code = EXIT_SKIP if g_args.skip_timeout else EXIT_FAILURE
            print("Timeout - Flags: {}".format(benchmark_info.command_line_args))
        elif benchmark_info.compare_outputs and output != benchmark_info.expected_output:
            exit_code = EXIT_FAILURE
            print("not ok - Flags: {}".format(benchmark_info.command_line_args))
            print()
            print("Standard output difference")
            print("=" * 80)
            print_diff(output, benchmark_info.expected_output)
            print("=" * 80)
            print()
            print()
            if error:
                print("Error output")
                print("=" * 80)
                print_colored(Color.YELLOW, error)
                print("=" * 80)
                print()
        elif benchmark_info.compare_outputs and error != benchmark_info.expected_error:
            exit_code = EXIT_FAILURE
            print(
                "not ok - Differences between expected and actual output on stderr - Flags: {}".format(
                    benchmark_info.command_line_args
                )
            )
            print()
            print("Error output difference")
            print("=" * 80)
            print_diff(error, benchmark_info.expected_error)
            print("=" * 80)
            print()
        elif exit_status != benchmark_info.expected_exit_status:
            exit_code = EXIT_FAILURE
            print(
                'not ok - Expected exit status "{}" but got "{}" - Flags: {}'.format(
                    benchmark_info.expected_exit_status,
                    exit_status,
                    benchmark_info.command_line_args,
                )
            )
            print()
            print("Output:")
            print("=" * 80)
            print_colored(Color.BLUE, output)
            print("=" * 80)
            print()
            print()
            print("Error output:")
            print("=" * 80)
            print_colored(Color.YELLOW, error)
            print("=" * 80)
            print()
        else:
            print("ok - Flags: {}".format(benchmark_info.command_line_args))
        return exit_code


################################################################################
# The testers
#
# Testers use `Tester` as a base class and implement `applies()` and `run()`
# methods. The `applies()` method returns `True` if a tester applies to a given
# benchmark and `run()` runs the actual test. Most testers can invoke the
# `run()` method in the base class, which calls the cvc5 binary with a set of
# arguments and checks the expected output (both stdout and stderr) as well as
# the exit status.
#
# To add a new tester, add a class and add it to the `g_tester` dictionary.
################################################################################


class BaseTester(Tester):
    def __init__(self):
        pass

    def run(self, benchmark_info):
        return super().run(benchmark_info)


class UnsatCoreTester(Tester):
    def __init__(self):
        pass

    def applies(self, benchmark_info):
        return (
            benchmark_info.benchmark_ext != ".sy"
            and (
                "unsat" in benchmark_info.expected_output.split()
                or "entailed" in benchmark_info.expected_output.split()
            )
            and "--no-produce-unsat-cores" not in benchmark_info.command_line_args
            and "--no-check-unsat-cores" not in benchmark_info.command_line_args
            and "--check-unsat-cores" not in benchmark_info.command_line_args
            and "sygus-inference" not in benchmark_info.benchmark_content
            and "--unconstrained-simp" not in benchmark_info.command_line_args
        )

    def run(self, benchmark_info):
        return super().run(
            benchmark_info._replace(
                command_line_args=benchmark_info.command_line_args
                + ["--check-unsat-cores"]
            )
        )


class ProofTester(Tester):
    def __init__(self):
        pass

    def applies(self, benchmark_info):
        expected_output_lines = benchmark_info.expected_output.split()
        return (
            benchmark_info.benchmark_ext != ".sy"
            and (
                "unsat" in benchmark_info.expected_output.split()
                or "entailed" in benchmark_info.expected_output.split()
            )
            and "--no-produce-proofs" not in benchmark_info.command_line_args
            and "--no-check-proofs" not in benchmark_info.command_line_args
            and "--check-proofs" not in benchmark_info.command_line_args
        )

    def run(self, benchmark_info):
        return super().run(
            benchmark_info._replace(
                command_line_args=benchmark_info.command_line_args + ["--check-proofs", "--proof-granularity=theory-rewrite"]
            )
        )


class ModelTester(Tester):
    def __init__(self):
        pass

    def applies(self, benchmark_info):
        expected_output_lines = benchmark_info.expected_output.split()
        return (
            benchmark_info.benchmark_ext != ".sy"
            and ("sat" in expected_output_lines or "unknown" in expected_output_lines)
            and "--no-debug-check-models" not in benchmark_info.command_line_args
            and "--no-check-models" not in benchmark_info.command_line_args
            and "--debug-check-models" not in benchmark_info.command_line_args
        )

    def run(self, benchmark_info):
        return super().run(
            benchmark_info._replace(
                command_line_args=benchmark_info.command_line_args
                + ["--debug-check-models"]
            )
        )


class SynthTester(Tester):
    def __init__(self):
        pass

    def applies(self, benchmark_info):
        return (
            benchmark_info.benchmark_ext == ".sy"
            and "--no-check-synth-sol" not in benchmark_info.command_line_args
            and "--sygus-rr" not in benchmark_info.command_line_args
            and "--check-synth-sol" not in benchmark_info.command_line_args
        )

    def run(self, benchmark_info):
        return super().run(
            benchmark_info._replace(
                command_line_args=benchmark_info.command_line_args
                + ["--check-synth-sol"]
            )
        )


class AbductTester(Tester):
    def __init__(self):
        pass

    def applies(self, benchmark_info):
        return (
            benchmark_info.benchmark_ext != ".sy"
            and "--no-check-abducts" not in benchmark_info.command_line_args
            and "--check-abducts" not in benchmark_info.command_line_args
            and "get-abduct" in benchmark_info.benchmark_content
        )

    def run(self, benchmark_info):
        return super().run(
            benchmark_info._replace(
                command_line_args=benchmark_info.command_line_args + ["--check-abducts"]
            )
        )


class DumpTester(Tester):
    def applies(self, benchmark_info):
        return benchmark_info.benchmark_ext != ".p"

    def run(self, benchmark_info):
        ext_to_lang = {
            ".smt2": "smt2",
            ".sy": "sygus",
        }

        tmpf_name = None
        with tempfile.NamedTemporaryFile(delete=False) as tmpf:
            dump_args = [
                "--parse-only",
                "-o",
                "raw-benchmark",
                "--output-lang={}".format(ext_to_lang[benchmark_info.benchmark_ext]),
            ]
            dump_output, _, _ = run_process(
                [benchmark_info.cvc5_binary]
                + benchmark_info.command_line_args
                + dump_args
                + [benchmark_info.benchmark_basename],
                benchmark_info.benchmark_dir,
                benchmark_info.timeout,
            )

            tmpf_name = tmpf.name
            tmpf.write(dump_output)

        if not tmpf_name:
            return EXIT_FAILURE

        exit_code = super().run(
            benchmark_info._replace(
                command_line_args=benchmark_info.command_line_args
                + [
                    "--parse-only",
                    "--lang={}".format(ext_to_lang[benchmark_info.benchmark_ext]),
                ],
                benchmark_basename=tmpf.name,
                expected_exit_status=0,
                compare_outputs=False,
            )
        )
        os.remove(tmpf.name)
        return exit_code


g_testers = {
    "base": BaseTester(),
    "unsat-core": UnsatCoreTester(),
    "proof": ProofTester(),
    "model": ModelTester(),
    "synth": SynthTester(),
    "abduct": AbductTester(),
    "dump": DumpTester(),
}

g_default_testers = [
    "base",
    "unsat-core",
    "proof",
    "model",
    "synth",
    "abduct",
]

################################################################################

BenchmarkInfo = collections.namedtuple(
    "BenchmarkInfo",
    [
        "wrapper",
        "scrubber",
        "error_scrubber",
        "timeout",
        "cvc5_binary",
        "benchmark_dir",
        "benchmark_basename",
        "benchmark_ext",
        "benchmark_content",
        "expected_output",
        "expected_error",
        "expected_exit_status",
        "command_line_args",
        "compare_outputs",
    ],
)

SCRUBBER = "SCRUBBER:"
ERROR_SCRUBBER = "ERROR-SCRUBBER:"
EXPECT = "EXPECT:"
EXPECT_ERROR = "EXPECT-ERROR:"
EXIT = "EXIT:"
COMMAND_LINE = "COMMAND-LINE:"
REQUIRES = "REQUIRES:"
DISABLE_TESTER = "DISABLE-TESTER:"

EXIT_OK = 0
EXIT_FAILURE = 1
EXIT_SKIP = 77
STATUS_TIMEOUT = 124


def print_colored(color, text):
    """Prints `text` in color `color`."""

    for line in text.splitlines():
        print(color + line + Color.ENDC)


def print_diff(actual, expected):
    """Prints the difference between `actual` and `expected`."""

    for line in difflib.unified_diff(
        expected.splitlines(), actual.splitlines(), "expected", "actual", lineterm=""
    ):
        if line.startswith("+"):
            print_colored(Color.GREEN, line)
        elif line.startswith("-"):
            print_colored(Color.RED, line)
        else:
            print(line)


def run_process(args, cwd, timeout, s_input=None):
    """Runs a process with a timeout `timeout` in seconds. `args` are the
    arguments to execute, `cwd` is the working directory and `s_input` is the
    input to be sent to the process over stdin. If `args` is a list, the
    arguments are escaped and concatenated. If `args` is a string, it is
    executed as-is (without additional escaping. Returns the output, the error
    output and the exit code of the process. If the process times out, the
    output and the error output are empty and the exit code is 124."""

    cmd = " ".join([shlex.quote(a) for a in args]) if isinstance(args, list) else args

    out = ""
    err = ""
    exit_status = STATUS_TIMEOUT
    try:
        # Instead of setting shell=True, we explicitly call bash. Using
        # shell=True seems to produce different exit codes on different
        # platforms under certain circumstances.
        res = subprocess.run(
            ["bash", "-c", cmd],
            cwd=cwd,
            input=s_input,
            timeout=timeout,
            stderr=subprocess.PIPE,
            stdout=subprocess.PIPE,
        )
        out = res.stdout
        err = res.stderr
        exit_status = res.returncode
    except subprocess.TimeoutExpired:
        exit_status = STATUS_TIMEOUT

    return out, err, exit_status


def get_cvc5_features(cvc5_binary):
    """Returns a list of features supported by the cvc5 binary `cvc5_binary`."""

    output, _, _ = run_process([cvc5_binary, "--show-config"], None, None)
    if isinstance(output, bytes):
        output = output.decode()

    features = []
    disabled_features = []
    for line in output.split("\n"):
        tokens = [t.strip() for t in line.split(":")]
        if len(tokens) == 2:
            key, value = tokens
            if value == "yes":
                features.append(key)
            elif value == "no":
                disabled_features.append(key)

    return features, disabled_features


def run_benchmark(benchmark_info):
    """Runs cvc5 on a benchmark with the given `benchmark_info`. It runs on the
    file `benchmark_basename` in the directory `benchmark_dir` using the binary
    `cvc5_binary` with the command line options `command_line_args`. The output
    is scrubbed using `scrubber` and `error_scrubber` for stdout and stderr,
    respectively."""

    bin_args = benchmark_info.wrapper[:]
    bin_args.append(benchmark_info.cvc5_binary)

    output = None
    error = None
    exit_status = None
    output, error, exit_status = run_process(
        bin_args
        + benchmark_info.command_line_args
        + [benchmark_info.benchmark_basename],
        benchmark_info.benchmark_dir,
        benchmark_info.timeout,
    )

    # If a scrubber command has been specified then apply it to the output.
    if benchmark_info.scrubber:
        output, _, _ = run_process(
            benchmark_info.scrubber,
            benchmark_info.benchmark_dir,
            benchmark_info.timeout,
            output,
        )
    if benchmark_info.error_scrubber:
        error, _, _ = run_process(
            benchmark_info.error_scrubber,
            benchmark_info.benchmark_dir,
            benchmark_info.timeout,
            error,
        )

    # Popen in Python 3 returns a bytes object instead of a string for
    # stdout/stderr.
    if isinstance(output, bytes):
        output = output.decode()
    if isinstance(error, bytes):
        error = error.decode()
    output = re.sub(r"^[ \t]*", "", output.strip(), flags=re.MULTILINE)
    error = re.sub(r"^[ \t]*", "", error.strip(), flags=re.MULTILINE)
    return (output, error, exit_status)


def run_regression(
    testers,
    wrapper,
    cvc5_binary,
    benchmark_path,
    timeout,
):
    """Determines the expected output for a benchmark, runs cvc5 on it using
    all the specified `testers` and then checks whether the output corresponds
    to the expected output. Optionally uses a wrapper `wrapper`."""

    if not os.access(cvc5_binary, os.X_OK):
        sys.exit('"{}" does not exist or is not executable'.format(cvc5_binary))
    if not os.path.isfile(benchmark_path):
        sys.exit('"{}" does not exist or is not a file'.format(benchmark_path))

    cvc5_features, cvc5_disabled_features = get_cvc5_features(cvc5_binary)

    basic_command_line_args = []

    benchmark_basename = os.path.basename(benchmark_path)
    benchmark_filename, benchmark_ext = os.path.splitext(benchmark_basename)
    benchmark_dir = os.path.dirname(benchmark_path)
    comment_char = "%"
    status_regex = None
    status_to_output = lambda s: s
    if benchmark_ext == ".smt2":
        status_regex = r"set-info\s*:status\s*(sat|unsat)"
        comment_char = ";"
    elif benchmark_ext == ".p":
        status_regex = (
            r"% Status\s*:\s*(Theorem|Unsatisfiable|CounterSatisfiable|Satisfiable)"
        )
        status_to_output = lambda s: "% SZS status {} for {}".format(
            s, benchmark_filename
        )
    elif benchmark_ext == ".sy":
        comment_char = ";"
    else:
        sys.exit('"{}" must be *.smt2 or *.p or *.sy'.format(benchmark_basename))

    benchmark_lines = None
    with open(benchmark_path, "r") as benchmark_file:
        benchmark_lines = benchmark_file.readlines()
    benchmark_content = "".join(benchmark_lines)

    # Extract the metadata for the benchmark.
    scrubber = None
    error_scrubber = None
    expected_output = ""
    expected_error = ""
    expected_exit_status = None
    command_lines = []
    requires = []
    for line in benchmark_lines:
        # Skip lines that do not start with a comment character.
        if line[0] != comment_char:
            continue
        line = line[1:].lstrip()

        if line.startswith(SCRUBBER):
            scrubber = line[len(SCRUBBER) :].strip()
        elif line.startswith(ERROR_SCRUBBER):
            error_scrubber = line[len(ERROR_SCRUBBER) :].strip()
        elif line.startswith(EXPECT):
            expected_output += line[len(EXPECT) :].strip() + "\n"
        elif line.startswith(EXPECT_ERROR):
            expected_error += line[len(EXPECT_ERROR) :].strip() + "\n"
        elif line.startswith(EXIT):
            expected_exit_status = int(line[len(EXIT) :].strip())
        elif line.startswith(COMMAND_LINE):
            command_lines.append(line[len(COMMAND_LINE) :].strip())
        elif line.startswith(REQUIRES):
            requires.append(line[len(REQUIRES) :].strip())
        elif line.startswith(DISABLE_TESTER):
            disable_tester = line[len(DISABLE_TESTER) :].strip()
            if disable_tester not in g_testers:
                print("Unknown tester: {}".format(disable_tester))
                return EXIT_FAILURE
            if disable_tester in testers:
                testers.remove(disable_tester)

    expected_output = expected_output.strip()
    expected_error = expected_error.strip()

    # Expected output/expected error has not been defined in the metadata for
    # the benchmark. Try to extract the information from the benchmark itself.
    if expected_output == "" and expected_error == "":
        match = None
        if status_regex:
            match = re.findall(status_regex, benchmark_content)

        if match:
            expected_output = status_to_output("\n".join(match))
        elif expected_exit_status is None:
            # If there is no expected output/error and the exit status has not
            # been set explicitly, the benchmark is invalid.
            sys.exit('Cannot determine status of "{}"'.format(benchmark_path))
    if expected_exit_status is None:
        expected_exit_status = 0

    if "CVC5_REGRESSION_ARGS" in os.environ:
        basic_command_line_args += shlex.split(os.environ["CVC5_REGRESSION_ARGS"])

    for req_feature in requires:
        is_negative = False
        if req_feature.startswith("no-"):
            req_feature = req_feature[len("no-") :]
            is_negative = True
        if req_feature not in (cvc5_features + cvc5_disabled_features):
            print(
                "Illegal requirement in regression: {}\nAllowed requirements: {}".format(
                    req_feature, " ".join(cvc5_features + cvc5_disabled_features)
                )
            )
            return EXIT_FAILURE
        if is_negative:
            if req_feature in cvc5_features:
                print(
                    "1..0 # Skipped regression: not valid with {}".format(req_feature)
                )
                return EXIT_SKIP if g_args.use_skip_return_code else EXIT_OK
        elif req_feature not in cvc5_features:
            print("1..0 # Skipped regression: {} not supported".format(req_feature))
            return EXIT_SKIP if g_args.use_skip_return_code else EXIT_OK

    if not command_lines:
        command_lines.append("")

    tests = []
    expected_output_lines = expected_output.split()
    command_line_args_configs = []
    for command_line in command_lines:
        args = shlex.split(command_line)
        all_args = basic_command_line_args + args

        command_line_args_configs.append(all_args)

        benchmark_info = BenchmarkInfo(
            wrapper=wrapper,
            scrubber=scrubber,
            error_scrubber=error_scrubber,
            timeout=timeout,
            cvc5_binary=cvc5_binary,
            benchmark_dir=benchmark_dir,
            benchmark_basename=benchmark_basename,
            benchmark_ext=benchmark_ext,
            benchmark_content=benchmark_content,
            expected_output=expected_output,
            expected_error=expected_error,
            expected_exit_status=expected_exit_status,
            command_line_args=all_args,
            compare_outputs=True,
        )
        for tester_name, tester in g_testers.items():
            if tester_name in testers and tester.applies(benchmark_info):
                tests.append((tester, benchmark_info))

    if len(tests) == 0:
        print("1..0 # Skipped regression: no tests to run")
        return EXIT_SKIP if g_args.use_skip_return_code else EXIT_OK

    print("1..{}".format(len(tests)))
    print("# Starting")
    # Run cvc5 on the benchmark with the different testers and check whether
    # the exit status, stdout output, stderr output are as expected.
    exit_code = EXIT_OK
    for tester, benchmark_info in tests:
        test_exit_code = tester.run(benchmark_info)
        if exit_code == EXIT_FAILURE or test_exit_code == EXIT_FAILURE:
            exit_code = EXIT_FAILURE
        else:
            exit_code = test_exit_code

    return exit_code


def main():
    """Parses the command line arguments and then calls the core of the
    script."""

    global g_args

    parser = argparse.ArgumentParser(
        description="Runs benchmark and checks for correct exit status and output."
    )
    parser.add_argument("--use-skip-return-code", action="store_true")
    parser.add_argument("--skip-timeout", action="store_true")
    parser.add_argument("--tester", choices=g_testers.keys(), action="append")
    parser.add_argument("wrapper", nargs="*")
    parser.add_argument("cvc5_binary")
    parser.add_argument("benchmark")

    argv = sys.argv[1:]
    # Append options passed via RUN_REGRESSION_ARGS to argv
    if os.environ.get("RUN_REGRESSION_ARGS"):
        argv.extend(shlex.split(os.getenv("RUN_REGRESSION_ARGS")))

    g_args = parser.parse_args(argv)

    cvc5_binary = os.path.abspath(g_args.cvc5_binary)

    wrapper = g_args.wrapper
    if os.environ.get("VALGRIND") == "1" and not wrapper:
        wrapper = ["libtool", "--mode=execute", "valgrind"]

    timeout = float(os.getenv("TEST_TIMEOUT", "600"))

    testers = g_args.tester
    if not testers:
        testers = g_default_testers

    return run_regression(
        testers,
        wrapper,
        cvc5_binary,
        g_args.benchmark,
        timeout,
    )


if __name__ == "__main__":
    exit_code = main()
    sys.exit(exit_code)
