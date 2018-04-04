# Regression

## Regression Levels and Running Regression Tests

CVC4's regression tests are divided into 5 levels (level 0 to 4). Higher
regression levels are reserved for longer running regressions. To run
regressions up to a certain level use `make regressX` where `X` designates the
level. `make regress` by default runs levels 0 and 1. On Travis, we only run
regression level 0 to keep the time short. During our nightly builds, we run
regression level 2.

To only run some benchmarks, you can use the `TEST_REGEX` environment variable.
For example:

```
TEST_REGEX=quantifiers make regress0
```

Runs regression tests from level 0 that have "quantifiers" in their name.

## Adding New Regressions

To add a new regression file, add the file to git, for example:

```
git add regress/regress0/testMyFunctionality.cvc
```

Also add it to [Makefile.tests](Makefile.tests) in this directory.

A number of regressions exist under test/regress that aren't listed in
[Makefile.tests](Makefile.tests). These are regressions that may someday be
included in the standard suite of tests, but aren't yet included (perhaps they
test functionality not yet supported).

## Expected Output, Error, and Exit Codes

In the regression file, you can specify expected stdout, stderr, and exit codes
with the following directives:

```
% EXPECT: stdout
% EXPECT-ERROR: stderr
% EXIT: 0
```

This example expects an exit status of 0 from CVC4, the single line "stderr" on
stderr, and the single line "stdout" on stdout. You can repeat `EXPECT` and
`EXPECT-ERROR` lines as many times as you like, and at different points of the
file.  This is useful for multiple queries:

```
% EXPECT: INVALID
QUERY FALSE;
% EXPECT: VALID
QUERY TRUE;
% EXPECT-ERROR: CVC4 Error:
% EXPECT-ERROR: Parse Error: regress.cvc:7.13: Unexpected token: 'error'.
syntax error;
% EXIT: 1
```

Note that the directives are in comments, so if the benchmark file is an smt2
file for example, the first character would be `;` instead of `%`.

Benchmark files can also specify the command line options to be used when
executing CVC4, for example:

```
% COMMAND-LINE: --incremental
```

Sometimes, the expected output or error output may need preprocessing. This is
done with the `SCRUBBER` and `ERROR-SCRUBBER` directives:

```
; SCRUBBER: sed -e 's/The fact in question: .*$/The fact in question: TERM/'
```

Sometimes it is useful to keep the directives separate. You can separate the
benchmark from the output expectations by putting the benchmark in `<benchmark
file>.smt` and the directives in `<benchmark file>.smt.expect`, which is looked
for by the regression script.
