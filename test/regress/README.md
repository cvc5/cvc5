# Regression

## Regression Levels and Running Regression Tests

CVC4's regression tests are divided into 5 levels (level 0 to 4). Higher
regression levels are reserved for longer running regressions. 

For running regressions tests, 
see the [INSTALL](https://github.com/CVC4/CVC4/blob/master/INSTALL.md#testing-cvc4) file.

By default, each invocation of CVC4 is done with a 10 minute timeout. To use a
different timeout, set the `TEST_TIMEOUT` environment variable:

```
TEST_TIMEOUT=0.5 ctest -L regress0
```

This runs regression tests from level 0 with a 0.5 second timeout.

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
- `*.cvc`: A benchmark that uses [CVC4's native input language](https://github.com/CVC4/CVC4/wiki/CVC4-Native-Input-Language)
- `*.sy`: A [SyGuS](http://sygus.seas.upenn.edu/files/SyGuS-IF.pdf) benchmark
- `*.p`: A [TPTP](http://www.cs.miami.edu/~tptp/TPTP/SyntaxBNF.html) benchmark

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

Sometimes, certain benchmarks only apply to certain CVC4
configurations. The `REQUIRES` directive can be used to only run
a given benchmark when a feature is supported. For example:

```
; REQUIRES: symfpu
```

This benchmark is only run when symfpu has been configured.  Multiple
`REQUIRES` directives are supported. For a list of features that can be listed
as a requirement, refer to CVC4's `--show-config` output. Features can also be
excluded by adding the `no-` prefix, e.g. `no-symfpu` means that the test is
not valid for builds that include symfpu support.
