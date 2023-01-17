# Regression

## Regression Levels

cvc5's regression tests are divided into 5 levels (level 0 to 4), based on
their run time (`production` build with `--assertions`).
Higher regression levels are reserved for longer running regressions.

The time limits for each level are:

* **Level 0:** <= 1s
* **Level 1:** <= 5s
* **Level 2:** <= 10s
* **Level 3:** <= 100s
* **Level 4:** > 100s

## Running Regression Tests

For running regressions tests, see the
[INSTALL](https://github.com/cvc5/cvc5/blob/main/INSTALL.rst#testing-cvc5)
file.

By default, each invocation of cvc5 is done with a 10 minute timeout. To use a
different timeout, set the `TEST_TIMEOUT` environment variable:

```
TEST_TIMEOUT=0.5 ctest -L regress0
```

This runs regression tests from level 0 with a 0.5 second timeout.

In order to run regressions with an option turned on, set the
`CVC5_REGRESSION_ARGS` environment variable:

```
CVC5_REGRESSION_ARGS="--ackermann" ctest -L regress0
```

This runs regression tests from level 0 with the `--ackermann` option.

## Adding New Regressions

To add a new regression file, add the file to git, for example:

```
git add regress/regress0/testMyFunctionality.cvc
```

Also add it to [CMakeLists.txt](CMakeLists.txt) in this directory.

A number of regressions exist under test/regress that are not listed in
[CMakeLists.txt](CMakeLists.txt). These are regressions that may someday be
included in the standard suite of tests, but are not yet included (perhaps they
test functionality not yet supported).

The following types of regression files are supported:

- `*.smt`: An [SMT1.x](http://smtlib.cs.uiowa.edu/papers/format-v1.2-r06.08.30.pdf) benchmark
- `*.smt2`: An [SMT 2.x](http://smtlib.cs.uiowa.edu/papers/smt-lib-reference-v2.6-r2017-07-18.pdf) benchmark
- `*.sy`: A [SyGuS](http://sygus.seas.upenn.edu/files/SyGuS-IF.pdf) benchmark
- `*.p`: A [TPTP](http://www.cs.miami.edu/~tptp/TPTP/SyntaxBNF.html) benchmark

## Directives

In the regression file, you can specify expected stdout, stderr, and exit codes
with the following directives:

```
% EXPECT: stdout
% EXPECT-ERROR: stderr
% EXIT: 0
```

This example expects an exit status of 0 from cvc5, the single line "stderr" on
stderr, and the single line "stdout" on stdout. You can repeat `EXPECT` and
`EXPECT-ERROR` lines as many times as you like, and at different points of the
file.  This is useful for multiple queries:

```
% EXPECT: INVALID
QUERY FALSE;
% EXPECT: VALID
QUERY TRUE;
% EXPECT-ERROR: cvc5 Error:
% EXPECT-ERROR: Parse Error: regress.cvc:7.13: Unexpected token: 'error'.
syntax error;
% EXIT: 1
```

Note that the directives are in comments, so if the benchmark file is an smt2
file for example, the first character would be `;` instead of `%`.

Benchmark files can also specify the command line options to be used when
executing cvc5, for example:

```
% COMMAND-LINE: --incremental
```

If multiple `COMMAND-LINE` directives are used, the regression is run with each
set of options separately.

Sometimes, the expected output or error output may need some processing. This
is done with the `SCRUBBER` and `ERROR-SCRUBBER` directives. The command
specified by the `SCRUBBER`/`ERROR-SCRUBBER` directive is applied to the output
before the the output is matched against the `EXPECT`/`EXPECT-ERROR` directives
respectively. For example:

```
; SCRUBBER: sed -e 's/The fact in question: .*$/The fact in question: TERM/' -e 's/in a linear logic: .*$/in a linear logic: TERM/'
; EXPECT: (error "A non-linear fact was asserted to arithmetic in a linear logic.
; EXPECT: The fact in question: TERM
; EXPECT: ")
```

The `SCRUBBER` directive in this example replaces the actual term by a fixed
string `TERM` to make the regression test robust to the actual term printed
(e.g. there could be multiple non-linear facts and it is ok if any of them is
printed).

Sometimes, certain benchmarks only apply to certain cvc5
configurations. The `REQUIRES` directive can be used to only run
a given benchmark when a feature is supported. For example:

```
; REQUIRES: cryptominisat
```

This benchmark is only run when CryptoMiniSat has been configured.  Multiple
`REQUIRES` directives are supported. For a list of features that can be listed
as a requirement, refer to cvc5's `--show-config` output. Features can also be
excluded by adding the `no-` prefix, e.g. `no-cryptominisat` means that the
test is not valid for builds that include CryptoMiniSat support.

To disable a specific type of test, the `DISABLE-TESTER` directive can be used.
The following example disables the abduct tester for a regression:

```
; DISABLE-TESTER: abduct
```

Multiple testers can be disabled using multiple `DISABLE-TESTER` directives. In
general, each `DISABLE-TESTER` directive disables only the specified tester. The
only exception to this rule is the proof tester. Disabling the proof tester,
which directs cvc5 to check generated proofs internally, also disables testers
that check the printed versions of those proofs (e.g., the lfsc tester).
