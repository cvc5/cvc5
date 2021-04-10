#!/usr/bin/env python3
#####################
## run_regression.py
## Top contributors (to current version):
##   Andres Noetzli, Yoni Zohar, Mathias Preiner
## This file is part of the CVC4 project.
## Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
## in the top-level source directory and their institutional affiliations.
## All rights reserved.  See the file COPYING in the top-level source
## directory for licensing information.
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


def get_cvc4_features(cvc4_binary):
    """Returns a list of features supported by the CVC4 binary `cvc4_binary`."""

    output, _, _ = run_process([cvc4_binary, '--show-config'], None, None)
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


def run_benchmark(dump, wrapper, scrubber, error_scrubber, cvc4_binary,
                  command_line, benchmark_dir, benchmark_filename, timeout):

    str1 = "CALL: "
    for ele in command_line: 
      str1 += ele
      str1 += " "
    str1 += benchmark_dir
    str1 += "/"
    str1 += benchmark_filename

    output = str1
    error = ''
    exit_status = EXIT_OK
    
    return (output.strip(), error.strip(), exit_status)


def run_regression(check_unsat_cores, check_proofs, dump, use_skip_return_code,
                   skip_timeout, wrapper, cvc4_binary, benchmark_path,
                   timeout):
    """Determines the expected output for a benchmark, runs CVC4 on it and then
    checks whether the output corresponds to the expected output. Optionally
    uses a wrapper `wrapper`, tests unsat cores (if check_unsat_cores is true),
    checks proofs (if check_proofs is true), or dumps a benchmark and uses that as
    the input (if dump is true). `use_skip_return_code` enables/disables
    returning 77 when a test is skipped."""

    if not os.access(cvc4_binary, os.X_OK):
        sys.exit(
            '"{}" does not exist or is not executable'.format(cvc4_binary))
    if not os.path.isfile(benchmark_path):
        sys.exit('"{}" does not exist or is not a file'.format(benchmark_path))

    cvc4_features, cvc4_disabled_features = get_cvc4_features(cvc4_binary)

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

    if 'CVC4_REGRESSION_ARGS' in os.environ:
        basic_command_line_args += shlex.split(
            os.environ['CVC4_REGRESSION_ARGS'])

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
        if req_feature not in (cvc4_features + cvc4_disabled_features):
            print(
                'Illegal requirement in regression: {}\nAllowed requirements: {}'
                .format(req_feature,
                        ' '.join(cvc4_features + cvc4_disabled_features)))
            return EXIT_FAILURE
        if is_negative:
            if req_feature in cvc4_features:
                print('1..0 # Skipped regression: not valid with {}'.format(
                    req_feature))
                return (EXIT_SKIP if use_skip_return_code else EXIT_OK)
        elif req_feature not in cvc4_features:
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

        #command_line_args_configs.append(all_args)

        expected_output_lines = expected_output.split()
        extra_command_line_args = []
        if 'unsat' in expected_output_lines or 'entailed' in expected_output_lines:
            if benchmark_ext != '.sy' and \
               '--dump-unsat-cores' not in all_args and \
               '--dump-unsat-cores-full' not in all_args and \
               '--no-produce-proofs' not in all_args and \
               '--no-check-proofs' not in all_args and \
               '-i' not in all_args and \
               '--incremental' not in all_args and \
               ':incremental true' not in benchmark_content and \
               '--global-negate' not in all_args and \
               ':global-negate true' not in benchmark_content and \
               '--produce-unsat-cores' not in all_args and \
               ':produce-unsat-cores true' not in benchmark_content and \
               '--sygus-inference' not in all_args and \
               ':sygus-inference true' not in benchmark_content:
                extra_command_line_args += ['--dump-proofs --proof-format=lfsc']

        # Create a test case for each extra argument
        for extra_arg in extra_command_line_args:
            command_line_args_configs.append(all_args + [extra_arg])

    # Run CVC4 on the benchmark with the different option sets and check
    # whether the exit status, stdout output, stderr output are as expected.
    exit_code = EXIT_OK
    for command_line_args in command_line_args_configs:
        output, error, exit_status = run_benchmark(dump, wrapper, scrubber,
                                                   error_scrubber, cvc4_binary,
                                                   command_line_args,
                                                   benchmark_dir,
                                                   benchmark_basename, timeout)
        output = re.sub(r'^[ \t]*', '', output, flags=re.MULTILINE)
        error = re.sub(r'^[ \t]*', '', error, flags=re.MULTILINE)
        print(output)
        print()
        exit_code = EXIT_FAILURE

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
    parser.add_argument('cvc4_binary')
    parser.add_argument('benchmark')

    argv = sys.argv[1:]
    # Append options passed via RUN_REGRESSION_ARGS to argv
    if os.environ.get('RUN_REGRESSION_ARGS'):
        argv.extend(shlex.split(os.getenv('RUN_REGRESSION_ARGS')))

    args = parser.parse_args(argv)

    cvc4_binary = os.path.abspath(args.cvc4_binary)

    wrapper = args.wrapper
    if os.environ.get('VALGRIND') == '1' and not wrapper:
        wrapper = ['libtool', '--mode=execute', 'valgrind']

    timeout = float(os.getenv('TEST_TIMEOUT', '600'))

    return run_regression(args.check_unsat_cores, args.check_proofs, args.dump,
                          args.use_skip_return_code, args.skip_timeout,
                          wrapper, cvc4_binary, args.benchmark, timeout)


if __name__ == "__main__":
    exit_code = main()
    sys.exit(exit_code)
