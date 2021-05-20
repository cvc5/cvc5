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
import difflib
import os
import re
import shlex
import subprocess
import sys
import threading


class Color:
    BLUE = '\033[94m'
    GREEN = '\033[92m'
    YELLOW = '\033[93m'
    RED = '\033[91m'
    ENDC = '\033[0m'


SCRUBBER = 'SCRUBBER:'
ERROR_SCRUBBER = 'ERROR-SCRUBBER:'
EXPECT = 'EXPECT:'
EXPECT_ERROR = 'EXPECT-ERROR:'
EXIT = 'EXIT:'
COMMAND_LINE = 'COMMAND-LINE:'
REQUIRES = 'REQUIRES:'

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

    for line in difflib.unified_diff(expected.splitlines(),
                                     actual.splitlines(),
                                     'expected',
                                     'actual',
                                     lineterm=''):
        if line.startswith('+'):
            print_colored(Color.GREEN, line)
        elif line.startswith('-'):
            print_colored(Color.RED, line)
        else:
            print(line)


def run_process(args, cwd, timeout, s_input=None):
    """Runs a process with a timeout `timeout` in seconds. `args` are the
    arguments to execute, `cwd` is the working directory and `s_input` is the
    input to be sent to the process over stdin. Returns the output, the error
    output and the exit code of the process. If the process times out, the
    output and the error output are empty and the exit code is 124."""

    proc = subprocess.Popen(args,
                            cwd=cwd,
                            stdin=subprocess.PIPE,
                            stdout=subprocess.PIPE,
                            stderr=subprocess.PIPE)

    out = ''
    err = ''
    exit_status = STATUS_TIMEOUT
    try:
        if timeout:
            timer = threading.Timer(timeout, lambda p: p.kill(), [proc])
            timer.start()
        out, err = proc.communicate(input=s_input)
        exit_status = proc.returncode
    finally:
        if timeout:
            # The timer killed the process and is not active anymore.
            if exit_status == -9 and not timer.is_alive():
                exit_status = STATUS_TIMEOUT
            timer.cancel()

    return out, err, exit_status


def get_cvc5_features(cvc5_binary):
    """Returns a list of features supported by the cvc5 binary `cvc5_binary`."""

    output, _, _ = run_process([cvc5_binary, '--show-config'], None, None)
    if isinstance(output, bytes):
        output = output.decode()

    features = []
    disabled_features = []
    for line in output.split('\n'):
        tokens = [t.strip() for t in line.split(':')]
        if len(tokens) == 2:
            key, value = tokens
            if value == 'yes':
                features.append(key)
            elif value == 'no':
                disabled_features.append(key)

    return features, disabled_features


def run_benchmark(dump, wrapper, scrubber, error_scrubber, cvc5_binary,
                  command_line, benchmark_dir, benchmark_filename, timeout):
    """Runs cvc5 on the file `benchmark_filename` in the directory
    `benchmark_dir` using the binary `cvc5_binary` with the command line
    options `command_line`. The output is scrubbed using `scrubber` and
    `error_scrubber` for stdout and stderr, respectively. If dump is true, the
    function first uses cvc5 to read in and dump the benchmark file and then
    uses that as input."""

    bin_args = wrapper[:]
    bin_args.append(cvc5_binary)

    output = None
    error = None
    exit_status = None
    if dump:
        dump_args = [
            '--preprocess-only', '--dump', 'raw-benchmark',
            '--output-lang=smt2', '-qq'
        ]
        dump_output, _, _ = run_process(
            bin_args + command_line + dump_args + [benchmark_filename],
            benchmark_dir, timeout)
        output, error, exit_status = run_process(
            bin_args + command_line + ['--lang=smt2', '-'], benchmark_dir,
            timeout, dump_output)
    else:
        output, error, exit_status = run_process(
            bin_args + command_line + [benchmark_filename], benchmark_dir,
            timeout)

    # If a scrubber command has been specified then apply it to the output.
    if scrubber:
        output, _, _ = run_process(shlex.split(scrubber), benchmark_dir,
                                   timeout, output)
    if error_scrubber:
        error, _, _ = run_process(shlex.split(error_scrubber), benchmark_dir,
                                  timeout, error)

    # Popen in Python 3 returns a bytes object instead of a string for
    # stdout/stderr.
    if isinstance(output, bytes):
        output = output.decode()
    if isinstance(error, bytes):
        error = error.decode()
    return (output.strip(), error.strip(), exit_status)


def run_regression(check_unsat_cores, check_proofs, dump, use_skip_return_code,
                   skip_timeout, wrapper, cvc5_binary, benchmark_path,
                   timeout):
    """Determines the expected output for a benchmark, runs cvc5 on it and then
    checks whether the output corresponds to the expected output. Optionally
    uses a wrapper `wrapper`, tests unsat cores (if check_unsat_cores is true),
    checks proofs (if check_proofs is true), or dumps a benchmark and uses that as
    the input (if dump is true). `use_skip_return_code` enables/disables
    returning 77 when a test is skipped."""

    if not os.access(cvc5_binary, os.X_OK):
        sys.exit(
            '"{}" does not exist or is not executable'.format(cvc5_binary))
    if not os.path.isfile(benchmark_path):
        sys.exit('"{}" does not exist or is not a file'.format(benchmark_path))

    cvc5_features, cvc5_disabled_features = get_cvc5_features(cvc5_binary)

    basic_command_line_args = []

    benchmark_basename = os.path.basename(benchmark_path)
    benchmark_filename, benchmark_ext = os.path.splitext(benchmark_basename)
    benchmark_dir = os.path.dirname(benchmark_path)
    comment_char = '%'
    status_regex = None
    status_to_output = lambda s: s
    if benchmark_ext == '.smt':
        status_regex = r':status\s*(sat|unsat)'
        comment_char = ';'
    elif benchmark_ext == '.smt2':
        status_regex = r'set-info\s*:status\s*(sat|unsat)'
        comment_char = ';'
    elif benchmark_ext == '.cvc':
        pass
    elif benchmark_ext == '.p':
        status_regex = r'% Status\s*:\s*(Theorem|Unsatisfiable|CounterSatisfiable|Satisfiable)'
        status_to_output = lambda s: '% SZS status {} for {}'.format(
            s, benchmark_filename)
    elif benchmark_ext == '.sy':
        comment_char = ';'
        # Do not check proofs/unsat-cores with .sy files
        check_unsat_cores = False
        check_proofs = False
    else:
        sys.exit('"{}" must be *.cvc or *.smt or *.smt2 or *.p or *.sy'.format(
            benchmark_basename))

    benchmark_lines = None
    with open(benchmark_path, 'r') as benchmark_file:
        benchmark_lines = benchmark_file.readlines()
    benchmark_content = ''.join(benchmark_lines)

    # Extract the metadata for the benchmark.
    scrubber = None
    error_scrubber = None
    expected_output = ''
    expected_error = ''
    expected_exit_status = None
    command_lines = []
    requires = []
    for line in benchmark_lines:
        # Skip lines that do not start with a comment character.
        if line[0] != comment_char:
            continue
        line = line[1:].lstrip()

        if line.startswith(SCRUBBER):
            scrubber = line[len(SCRUBBER):].strip()
        elif line.startswith(ERROR_SCRUBBER):
            error_scrubber = line[len(ERROR_SCRUBBER):].strip()
        elif line.startswith(EXPECT):
            expected_output += line[len(EXPECT):].strip() + '\n'
        elif line.startswith(EXPECT_ERROR):
            expected_error += line[len(EXPECT_ERROR):].strip() + '\n'
        elif line.startswith(EXIT):
            expected_exit_status = int(line[len(EXIT):].strip())
        elif line.startswith(COMMAND_LINE):
            command_lines.append(line[len(COMMAND_LINE):].strip())
        elif line.startswith(REQUIRES):
            requires.append(line[len(REQUIRES):].strip())
    expected_output = expected_output.strip()
    expected_error = expected_error.strip()

    # Expected output/expected error has not been defined in the metadata for
    # the benchmark. Try to extract the information from the benchmark itself.
    if expected_output == '' and expected_error == '':
        match = None
        if status_regex:
            match = re.findall(status_regex, benchmark_content)

        if match:
            expected_output = status_to_output('\n'.join(match))
        elif expected_exit_status is None:
            # If there is no expected output/error and the exit status has not
            # been set explicitly, the benchmark is invalid.
            sys.exit('Cannot determine status of "{}"'.format(benchmark_path))
    if expected_exit_status is None:
        expected_exit_status = 0

    if 'CVC5_REGRESSION_ARGS' in os.environ:
        basic_command_line_args += shlex.split(
            os.environ['CVC5_REGRESSION_ARGS'])

    if not check_unsat_cores and ('(get-unsat-core)' in benchmark_content
                            or '(get-unsat-assumptions)' in benchmark_content):
        print(
            '1..0 # Skipped regression: unsat cores not supported without proof support'
        )
        return (EXIT_SKIP if use_skip_return_code else EXIT_OK)

    for req_feature in requires:
        is_negative = False
        if req_feature.startswith("no-"):
            req_feature = req_feature[len("no-"):]
            is_negative = True
        if req_feature not in (cvc5_features + cvc5_disabled_features):
            print(
                'Illegal requirement in regression: {}\nAllowed requirements: {}'
                .format(req_feature,
                        ' '.join(cvc5_features + cvc5_disabled_features)))
            return EXIT_FAILURE
        if is_negative:
            if req_feature in cvc5_features:
                print('1..0 # Skipped regression: not valid with {}'.format(
                    req_feature))
                return (EXIT_SKIP if use_skip_return_code else EXIT_OK)
        elif req_feature not in cvc5_features:
            print('1..0 # Skipped regression: {} not supported'.format(
                req_feature))
            return (EXIT_SKIP if use_skip_return_code else EXIT_OK)

    if not command_lines:
        command_lines.append('')

    command_line_args_configs = []
    for command_line in command_lines:
        args = shlex.split(command_line)
        all_args = basic_command_line_args + args

        if not check_unsat_cores and ('--check-unsat-cores' in all_args):
            print(
                '# Skipped command line options ({}): unsat cores not supported without proof support'
                .format(all_args))
            continue
        if not check_proofs and '--dump-proofs' in all_args:
            print(
                '# Skipped command line options ({}): proof production not supported'
                .format(all_args))
            continue

        command_line_args_configs.append(all_args)

        expected_output_lines = expected_output.split()
        extra_command_line_args = []
        if benchmark_ext == '.sy' and \
            '--no-check-synth-sol' not in all_args and \
            '--sygus-rr' not in all_args and \
            '--check-synth-sol' not in all_args:
            all_args += ['--check-synth-sol']
        if ('sat' in expected_output_lines or \
            'not_entailed' in expected_output_lines or \
            'unknown' in expected_output_lines) and \
           '--no-debug-check-models' not in all_args and \
           '--no-check-models' not in all_args and \
           '--debug-check-models' not in all_args:
            extra_command_line_args += ['--debug-check-models']
        if 'unsat' in expected_output_lines or 'entailed' in expected_output_lines:
            if check_unsat_cores and \
               '--no-produce-unsat-cores' not in all_args and \
               '--no-check-unsat-cores' not in all_args and \
               '--check-unsat-cores' not in all_args and \
               'sygus-inference' not in benchmark_content and \
               '--unconstrained-simp' not in all_args:
                extra_command_line_args += ['--check-unsat-cores']
            if check_proofs and \
               '--no-produce-proofs' not in all_args and \
               '--no-check-proofs' not in all_args and \
               '--check-proofs' not in all_args:
                extra_command_line_args += ['--check-proofs']
        if '--no-check-abducts' not in all_args and \
            '--check-abducts' not in all_args and \
            'get-abduct' in benchmark_content:
            all_args += ['--check-abducts']

        # Create a test case for each extra argument
        for extra_arg in extra_command_line_args:
            command_line_args_configs.append(all_args + [extra_arg])

    # Run cvc5 on the benchmark with the different option sets and check
    # whether the exit status, stdout output, stderr output are as expected.
    print('1..{}'.format(len(command_line_args_configs)))
    print('# Starting')
    exit_code = EXIT_OK
    for command_line_args in command_line_args_configs:
        output, error, exit_status = run_benchmark(dump, wrapper, scrubber,
                                                   error_scrubber, cvc5_binary,
                                                   command_line_args,
                                                   benchmark_dir,
                                                   benchmark_basename, timeout)
        output = re.sub(r'^[ \t]*', '', output, flags=re.MULTILINE)
        error = re.sub(r'^[ \t]*', '', error, flags=re.MULTILINE)
        if exit_status == STATUS_TIMEOUT:
            exit_code = EXIT_SKIP if skip_timeout else EXIT_FAILURE
            print('Timeout - Flags: {}'.format(command_line_args))
        elif output != expected_output:
            exit_code = EXIT_FAILURE
            print('not ok - Flags: {}'.format(command_line_args))
            print()
            print('Standard output difference')
            print('=' * 80)
            print_diff(output, expected_output)
            print('=' * 80)
            print()
            print()
            if error:
                print('Error output')
                print('=' * 80)
                print_colored(Color.YELLOW, error)
                print('=' * 80)
                print()
        elif error != expected_error:
            exit_code = EXIT_FAILURE
            print(
                'not ok - Differences between expected and actual output on stderr - Flags: {}'
                .format(command_line_args))
            print()
            print('Error output difference')
            print('=' * 80)
            print_diff(error, expected_error)
            print('=' * 80)
            print()
        elif expected_exit_status != exit_status:
            exit_code = EXIT_FAILURE
            print(
                'not ok - Expected exit status "{}" but got "{}" - Flags: {}'.
                format(expected_exit_status, exit_status, command_line_args))
            print()
            print('Output:')
            print('=' * 80)
            print_colored(Color.BLUE, output)
            print('=' * 80)
            print()
            print()
            print('Error output:')
            print('=' * 80)
            print_colored(Color.YELLOW, error)
            print('=' * 80)
            print()
        else:
            print('ok - Flags: {}'.format(command_line_args))

    return exit_code


def main():
    """Parses the command line arguments and then calls the core of the
    script."""

    parser = argparse.ArgumentParser(
        description=
        'Runs benchmark and checks for correct exit status and output.')
    parser.add_argument('--dump', action='store_true')
    parser.add_argument('--use-skip-return-code', action='store_true')
    parser.add_argument('--skip-timeout', action='store_true')
    parser.add_argument('--check-unsat-cores', action='store_true',
                        default=True)
    parser.add_argument('--no-check-unsat-cores', dest='check_unsat_cores',
                        action='store_false')
    parser.add_argument('--check-proofs', action='store_true', default=True)
    parser.add_argument('--no-check-proofs', dest='check_proofs',
                        action='store_false')
    parser.add_argument('wrapper', nargs='*')
    parser.add_argument('cvc5_binary')
    parser.add_argument('benchmark')

    argv = sys.argv[1:]
    # Append options passed via RUN_REGRESSION_ARGS to argv
    if os.environ.get('RUN_REGRESSION_ARGS'):
        argv.extend(shlex.split(os.getenv('RUN_REGRESSION_ARGS')))

    args = parser.parse_args(argv)

    cvc5_binary = os.path.abspath(args.cvc5_binary)

    wrapper = args.wrapper
    if os.environ.get('VALGRIND') == '1' and not wrapper:
        wrapper = ['libtool', '--mode=execute', 'valgrind']

    timeout = float(os.getenv('TEST_TIMEOUT', '600'))

    return run_regression(args.check_unsat_cores, args.check_proofs, args.dump,
                          args.use_skip_return_code, args.skip_timeout,
                          wrapper, cvc5_binary, args.benchmark, timeout)


if __name__ == "__main__":
    exit_code = main()
    sys.exit(exit_code)
