#!/usr/bin/env python3
"""
Usage:

    run_regression.py [--enable-proof] [--with-lfsc] [--dump]
        [--use-skip-return-code] [wrapper] cvc4-binary
        [benchmark.cvc | benchmark.smt | benchmark.smt2 | benchmark.p]

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

SCRUBBER = 'SCRUBBER: '
ERROR_SCRUBBER = 'ERROR-SCRUBBER: '
EXPECT = 'EXPECT: '
EXPECT_ERROR = 'EXPECT-ERROR: '
EXIT = 'EXIT: '
COMMAND_LINE = 'COMMAND-LINE: '
REQUIRES = 'REQUIRES: '

EXIT_OK = 0
EXIT_FAILURE = 1
EXIT_SKIP = 77


def run_process(args, cwd, timeout, s_input=None):
    """Runs a process with a timeout `timeout` in seconds. `args` are the
    arguments to execute, `cwd` is the working directory and `s_input` is the
    input to be sent to the process over stdin. Returns the output, the error
    output and the exit code of the process. If the process times out, the
    output and the error output are empty and the exit code is 124."""

    proc = subprocess.Popen(
        args,
        cwd=cwd,
        stdin=subprocess.PIPE,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE)

    out = ''
    err = ''
    exit_status = 124
    try:
        if timeout:
            timer = threading.Timer(timeout, lambda p: p.kill(), [proc])
            timer.start()
        out, err = proc.communicate(input=s_input)
        exit_status = proc.returncode
    finally:
        if timeout:
            timer.cancel()

    return out, err, exit_status


def get_cvc4_features(cvc4_binary):
    """Returns a list of features supported by the CVC4 binary `cvc4_binary`."""

    output, _, _ = run_process([cvc4_binary, '--show-config'], None, None)
    if isinstance(output, bytes):
        output = output.decode()

    features = []
    for line in output.split('\n'):
        tokens = [t.strip() for t in line.split(':')]
        if len(tokens) == 2:
            key, value = tokens
            if value == 'yes':
                features.append(key)

    return features


def logic_supported_with_proofs(logic):
    assert logic is None or isinstance(logic, str)
    return logic in [
            #single theories
            "QF_BV",
            "QF_UF",
            "QF_A",
            "QF_LRA",
            #two theories
            "QF_UFBV",
            "QF_UFLRA",
            "QF_AUF",
            "QF_ALRA",
            "QF_ABV",
            "QF_BVLRA"
            #three theories
            "QF_AUFBV",
            "QF_ABVLRA",
            "QF_UFBVLRA",
            "QF_AUFLRA",
            #four theories
            "QF_AUFBVLRA"
            ]

def run_benchmark(dump, wrapper, scrubber, error_scrubber, cvc4_binary,
                  command_line, benchmark_dir, benchmark_filename, timeout):
    """Runs CVC4 on the file `benchmark_filename` in the directory
    `benchmark_dir` using the binary `cvc4_binary` with the command line
    options `command_line`. The output is scrubbed using `scrubber` and
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
        output, _, _ = run_process(
            shlex.split(scrubber), benchmark_dir, timeout, output)
    if error_scrubber:
        error, _, _ = run_process(
            shlex.split(error_scrubber), benchmark_dir, timeout, error)

    # Popen in Python 3 returns a bytes object instead of a string for
    # stdout/stderr.
    if isinstance(output, bytes):
        output = output.decode()
    if isinstance(error, bytes):
        error = error.decode()
    return (output.strip(), error.strip(), exit_status)


def run_regression(unsat_cores, proofs, dump, use_skip_return_code, wrapper,
                   cvc4_binary, benchmark_path, timeout):
    """Determines the expected output for a benchmark, runs CVC4 on it and then
    checks whether the output corresponds to the expected output. Optionally
    uses a wrapper `wrapper`, tests unsat cores (if unsat_cores is true),
    checks proofs (if proofs is true), or dumps a benchmark and uses that as
    the input (if dump is true). `use_skip_return_code` enables/disables
    returning 77 when a test is skipped."""

    if not os.access(cvc4_binary, os.X_OK):
        sys.exit(
            '"{}" does not exist or is not executable'.format(cvc4_binary))
    if not os.path.isfile(benchmark_path):
        sys.exit('"{}" does not exist or is not a file'.format(benchmark_path))

    cvc4_features = get_cvc4_features(cvc4_binary)

    basic_command_line_args = []

    benchmark_basename = os.path.basename(benchmark_path)
    benchmark_filename, benchmark_ext = os.path.splitext(benchmark_basename)
    benchmark_dir = os.path.dirname(benchmark_path)
    comment_char = '%'
    status_regex = None
    logic_regex = None
    status_to_output = lambda s: s
    if benchmark_ext == '.smt':
        status_regex = r':status\s*(sat|unsat)'
        comment_char = ';'
    elif benchmark_ext == '.smt2':
        status_regex = r'set-info\s*:status\s*(sat|unsat)'
        logic_regex = r'\(\s*set-logic\s*(.*)\)'
        comment_char = ';'
    elif benchmark_ext == '.cvc':
        pass
    elif benchmark_ext == '.p':
        status_regex = r'% Status\s*:\s*(Theorem|Unsatisfiable|CounterSatisfiable|Satisfiable)'
        status_to_output = lambda s: '% SZS status {} for {}'.format(s, benchmark_filename)
    elif benchmark_ext == '.sy':
        comment_char = ';'
        # Do not use proofs/unsat-cores with .sy files
        unsat_cores = False
        proofs = False
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
    logic = None
    for line in benchmark_lines:
        # Skip lines that do not start with a comment character.
        if line[0] != comment_char:
            continue
        line = line[1:].lstrip()

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
            command_lines.append(line[len(COMMAND_LINE):])
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
    if logic_regex:
        logic_match = re.findall(logic_regex, benchmark_content)
        if logic_match and len(logic_match) == 1:
            logic = logic_match[0]

    if 'CVC4_REGRESSION_ARGS' in os.environ:
        basic_command_line_args += shlex.split(
            os.environ['CVC4_REGRESSION_ARGS'])

    if not unsat_cores and ('(get-unsat-core)' in benchmark_content
                            or '(get-unsat-assumptions)' in benchmark_content):
        print(
            '1..0 # Skipped regression: unsat cores not supported without proof support'
        )
        return (EXIT_SKIP if use_skip_return_code else EXIT_OK)

    for req_feature in requires:
        if req_feature.startswith("no-"):
            inv_feature = req_feature[len("no-"):]
            if inv_feature in cvc4_features:
                print('1..0 # Skipped regression: not valid with {}'.format(
                    inv_feature))
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

        if not unsat_cores and ('--check-unsat-cores' in all_args):
            print(
                '# Skipped command line options ({}): unsat cores not supported without proof support'
                .format(all_args))
            continue
        if not proofs and ('--check-proofs' in all_args
                           or '--dump-proofs' in all_args):
            print(
                '# Skipped command line options ({}): checking proofs not supported without LFSC support'
                .format(all_args))
            continue

        command_line_args_configs.append(all_args)

        extra_command_line_args = []
        if benchmark_ext == '.sy' and \
            '--no-check-synth-sol' not in all_args and \
            '--sygus-rr' not in all_args and \
            '--check-synth-sol' not in all_args:
            extra_command_line_args = ['--check-synth-sol']
        if re.search(r'^(sat|invalid|unknown)$', expected_output) and \
           '--no-check-models' not in all_args and \
           '--check-models' not in all_args:
            extra_command_line_args = ['--check-models']
        if proofs and re.search(r'^(unsat|valid)$', expected_output):
            if '--no-check-proofs' not in all_args and \
               '--check-proofs' not in all_args and \
               '--incremental' not in all_args and \
               '--unconstrained-simp' not in all_args and \
               logic_supported_with_proofs(logic) and \
               not cvc4_binary.endswith('pcvc4'):
                extra_command_line_args = ['--check-proofs']
        if unsat_cores and re.search(r'^(unsat|valid)$', expected_output):
            if '--no-check-unsat-cores' not in all_args and \
               '--check-unsat-cores' not in all_args and \
               '--incremental' not in all_args and \
               '--unconstrained-simp' not in all_args and \
               not cvc4_binary.endswith('pcvc4'):
                extra_command_line_args += ['--check-unsat-cores']
        if '--no-check-abducts' not in all_args and \
            '--check-abducts' not in all_args and \
            not cvc4_binary.endswith('pcvc4'):
            extra_command_line_args += ['--check-abducts']
        if extra_command_line_args:
            command_line_args_configs.append(all_args +
                                             extra_command_line_args)

    # Run CVC4 on the benchmark with the different option sets and check
    # whether the exit status, stdout output, stderr output are as expected.
    print('1..{}'.format(len(command_line_args_configs)))
    print('# Starting')
    exit_code = EXIT_OK
    for command_line_args in command_line_args_configs:
        output, error, exit_status = run_benchmark(
            dump, wrapper, scrubber, error_scrubber, cvc4_binary,
            command_line_args, benchmark_dir, benchmark_basename, timeout)
        if output != expected_output:
            exit_code = EXIT_FAILURE
            print(
                'not ok - Differences between expected and actual output on stdout - Flags: {}'
                .format(command_line_args))
            for line in difflib.context_diff(output.splitlines(),
                                             expected_output.splitlines()):
                print(line)
            print()
            print('Error output:')
            print(error)
        elif error != expected_error:
            exit_code = EXIT_FAILURE
            print(
                'not ok - Differences between expected and actual output on stderr - Flags: {}'
                .format(command_line_args))
            for line in difflib.context_diff(error.splitlines(),
                                             expected_error.splitlines()):
                print(line)
        elif expected_exit_status != exit_status:
            exit_code = EXIT_FAILURE
            print(
                'not ok - Expected exit status "{}" but got "{}" - Flags: {}'.
                format(expected_exit_status, exit_status, command_line_args))
            print()
            print('Output:')
            print(output)
            print()
            print('Error output:')
            print(error)
        else:
            print('ok - Flags: {}'.format(command_line_args))

    return exit_code


def main():
    """Parses the command line arguments and then calls the core of the
    script."""

    parser = argparse.ArgumentParser(
        description=
        'Runs benchmark and checks for correct exit status and output.')
    parser.add_argument('--enable-proof', action='store_true')
    parser.add_argument('--with-lfsc', action='store_true')
    parser.add_argument('--dump', action='store_true')
    parser.add_argument('--use-skip-return-code', action='store_true')
    parser.add_argument('wrapper', nargs='*')
    parser.add_argument('cvc4_binary')
    parser.add_argument('benchmark')
    args = parser.parse_args()
    cvc4_binary = os.path.abspath(args.cvc4_binary)

    wrapper = args.wrapper
    if os.environ.get('VALGRIND') == '1' and not wrapper:
        wrapper = ['libtool', '--mode=execute', 'valgrind']

    timeout = float(os.getenv('TEST_TIMEOUT', 600.0))

    return run_regression(args.enable_proof, args.with_lfsc, args.dump,
                          args.use_skip_return_code, wrapper, cvc4_binary,
                          args.benchmark, timeout)


if __name__ == "__main__":
    exit_code = main()
    sys.exit(exit_code)
