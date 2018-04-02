#!/usr/bin/env python3
"""
Usage:

    run_regression.py [ --proof | --dump ] [ wrapper ] cvc4-binary
        [ benchmark.cvc | benchmark.smt | benchmark.smt2 | benchmark.p ]

Runs benchmark and checks for correct exit status and output.
"""

import argparse
import difflib
import os
import re
import shlex
import subprocess
import sys

SCRUBBER = 'SCRUBBER: '
ERROR_SCRUBBER = 'ERROR-SCRUBBER: '
EXPECT = 'EXPECT: '
EXPECT_ERROR = 'EXPECT-ERROR: '
EXIT = 'EXIT: '
COMMAND_LINE = 'COMMAND-LINE: '


def run_benchmark(dump, wrapper, scrubber, error_scrubber, cvc4_binary,
                  command_line, benchmark_dir, benchmark_filename):
    """Runs CVC4 on the file `benchmark_file` in the directory `benchmark_dir`
    using the binary `cvc4_binary` with the command line options
    `command_line`. The output is scrubbed using `scrubber` and
    `error_scrubber` for stdout and stderr, respectively. If dump is true, the
    function first uses CVC4 to read in and dump the benchmark file and then
    uses that as input."""

    bin_args = wrapper[:]
    bin_args.append(cvc4_binary)

    output = None
    error = None
    exit_status = None
    if dump:
        dump_args = [
            '--preprocess-only', '--dump', 'raw-benchmark',
            '--output-lang=smt2', '-qq'
        ]
        dump_process = subprocess.Popen(
            bin_args + command_line + dump_args + [benchmark_filename],
            cwd=benchmark_dir,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE)
        dump_output, _ = dump_process.communicate()
        process = subprocess.Popen(
            bin_args + command_line + ['--lang=smt2', '-'],
            cwd=benchmark_dir,
            stdin=subprocess.PIPE,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE)
        output, error = process.communicate(input=dump_output)
        exit_status = process.returncode
    else:
        process = subprocess.Popen(
            bin_args + command_line + [benchmark_filename],
            cwd=benchmark_dir,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE)
        output, error = process.communicate()
        exit_status = process.returncode

    # If a scrubber command has been specified then apply it to the output.
    if scrubber:
        scrubber_process = subprocess.Popen(
            shlex.split(scrubber),
            stdin=subprocess.PIPE,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE)
        output, _ = scrubber_process.communicate(input=output)
    if error_scrubber:
        error_scrubber_process = subprocess.Popen(
            shlex.split(error_scrubber),
            stdin=subprocess.PIPE,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE)
        error, _ = error_scrubber_process.communicate(input=error)

    # Popen in Python 3 returns a bytes object instead of a string for
    # stdout/stderr.
    if isinstance(output, bytes):
        output = output.decode()
    if isinstance(error, bytes):
        error = error.decode()
    return (output.strip(), error.strip(), exit_status)


def run_regression(proof, dump, wrapper, cvc4_binary, benchmark_path):
    """Determines the expected output for a benchmark, runs CVC4 on it and then
    checks whether the output corresponds to the expected output. Optionally
    uses a wrapper `wrapper`, tests proof generation (if proof is true), or
    dumps a benchmark and uses that as the input (if dump is true)."""

    if not os.access(cvc4_binary, os.X_OK):
        sys.exit(
            '"{}" does not exist or is not executable'.format(cvc4_binary))
    if not os.path.isfile(benchmark_path):
        sys.exit('"{}" does not exist or is not a file'.format(benchmark_path))

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
        basic_command_line_args.append('--finite-model-find')
        status_regex = r'% Status\s*:\s*(Theorem|Unsatisfiable|CounterSatisfiable|Satisfiable)'
        status_to_output = lambda s: '% SZS status {} for {}'.format(s, benchmark_filename)
    elif benchmark_ext == '.sy':
        comment_char = ';'
        # Do not use proofs/unsat-cores with .sy files
        proof = False
    else:
        sys.exit('"{}" must be *.cvc or *.smt or *.smt2 or *.p or *.sy'.format(
            benchmark_basename))

    # If there is an ".expect" file for the benchmark, read the metadata
    # from there, otherwise from the benchmark file.
    metadata_filename = benchmark_path + '.expect'
    if os.path.isfile(metadata_filename):
        comment_char = '%'
    else:
        metadata_filename = benchmark_path

    metadata_lines = None
    with open(metadata_filename, 'r') as metadata_file:
        metadata_lines = metadata_file.readlines()
    metadata_content = ''.join(metadata_lines)

    # Extract the metadata for the benchmark.
    scrubber = None
    error_scrubber = None
    expected_output = ''
    expected_error = ''
    expected_exit_status = None
    command_line = ''
    for line in metadata_lines:
        # Skip lines that do not start with "%"
        if line[0] != comment_char:
            continue
        line = line[2:]

        if line.startswith(SCRUBBER):
            scrubber = line[len(SCRUBBER):]
        elif line.startswith(ERROR_SCRUBBER):
            error_scrubber = line[len(ERROR_SCRUBBER):]
        elif line.startswith(EXPECT):
            expected_output += line[len(EXPECT):]
        elif line.startswith(EXPECT_ERROR):
            expected_error += line[len(EXPECT_ERROR):]
        elif line.startswith(EXIT):
            expected_exit_status = int(line[len(EXIT):])
        elif line.startswith(COMMAND_LINE):
            command_line += line[len(COMMAND_LINE):]
    expected_output = expected_output.strip()
    expected_error = expected_error.strip()

    # Expected output/expected error has not been defined in the metadata for
    # the benchmark. Try to extract the information from the benchmark itself.
    if expected_output == '' and expected_error == '':
        match = None
        if status_regex:
            match = re.search(status_regex, metadata_content)

        if match:
            expected_output = status_to_output(match.group(1))
        elif expected_exit_status is None:
            # If there is no expected output/error and the exit status has not
            # been set explicitly, the benchmark is invalid.
            sys.exit('Cannot determine status of "{}"'.format(benchmark_path))

    if not proof and ('(get-unsat-cores)' in metadata_content
                      or '(get-unsat-assumptions)' in metadata_content):
        print(
            '1..0 # Skipped: unsat cores not supported without proof support')
        return

    if expected_exit_status is None:
        expected_exit_status = 0

    if 'CVC4_REGRESSION_ARGS' in os.environ:
        basic_command_line_args += shlex.split(
            os.environ['CVC4_REGRESSION_ARGS'])
    basic_command_line_args += shlex.split(command_line)
    command_line_args_configs = [basic_command_line_args]

    extra_command_line_args = []
    if benchmark_ext == '.sy' and \
        '--no-check-synth-sol' not in basic_command_line_args and \
        '--check-synth-sol' not in basic_command_line_args:
        extra_command_line_args = ['--check-synth-sol']
    if re.search(r'^(sat|invalid|unknown)$', expected_output) and \
       '--no-check-models' not in basic_command_line_args:
        extra_command_line_args = ['--check-models']
    if proof and re.search(r'^(sat|valid)$', expected_output):
        if '--no-check-proofs' not in basic_command_line_args and \
           '--incremental' not in basic_command_line_args and \
           '--unconstrained-simp' not in basic_command_line_args and \
           not cvc4_binary.endswith('pcvc4'):
            extra_command_line_args = [
                '--check-proofs', '--no-bv-eq', '--no-bv-ineq',
                '--no-bv-algebraic'
            ]
        if '--no-check-unsat-cores' not in basic_command_line_args and \
           '--incremental' not in basic_command_line_args and \
           '--unconstrained-simp' not in basic_command_line_args and \
           not cvc4_binary.endswith('pcvc4'):
            extra_command_line_args = [
                '--check-proofs', '--no-bv-eq', '--no-bv-ineq',
                '--no-bv-algebraic'
            ]
    if extra_command_line_args:
        command_line_args_configs.append(
            basic_command_line_args + extra_command_line_args)

    # Run CVC4 on the benchmark with the different option sets and check
    # whether the exit status, stdout output, stderr output are as expected.
    print('1..{}'.format(len(command_line_args_configs)))
    print('# Starting')
    for command_line_args in command_line_args_configs:
        output, error, exit_status = run_benchmark(
            dump, wrapper, scrubber, error_scrubber, cvc4_binary,
            command_line_args, benchmark_dir, benchmark_basename)
        if output != expected_output:
            print(
                'not ok - Differences between expected and actual output on stdout - Flags: {}'.
                format(command_line_args))
            for line in difflib.context_diff(output.splitlines(),
                                             expected_output.splitlines()):
                print(line)
        elif error != expected_error:
            print(
                'not ok - Differences between expected and actual output on stderr - Flags: {}'.
                format(command_line_args))
            for line in difflib.context_diff(error.splitlines(),
                                             expected_error.splitlines()):
                print(line)
        elif expected_exit_status != exit_status:
            print(
                'not ok - Expected exit status "{}" but got "{}" - Flags: {}'.
                format(expected_exit_status, exit_status, command_line_args))
        else:
            print('ok - Flags: {}'.format(command_line_args))


def main():
    """Parses the command line arguments and then calls the core of the
    script."""

    parser = argparse.ArgumentParser(
        description=
        'Runs benchmark and checks for correct exit status and output.')
    parser.add_argument('--proof', action='store_true')
    parser.add_argument('--dump', action='store_true')
    parser.add_argument('wrapper', nargs='*')
    parser.add_argument('cvc4_binary')
    parser.add_argument('benchmark')
    args = parser.parse_args()
    cvc4_binary = os.path.abspath(args.cvc4_binary)

    wrapper = args.wrapper
    if os.environ.get('VALGRIND') == '1' and not wrapper:
        wrapper = ['libtool', '--mode=execute', 'valgrind']

    run_regression(args.proof, args.dump, wrapper, cvc4_binary, args.benchmark)


if __name__ == "__main__":
    main()
