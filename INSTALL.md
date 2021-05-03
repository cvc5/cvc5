cvc5 prerelease version 1.0
===========================

## Building cvc5

    ./configure.sh
        # use --prefix to specify an install prefix (default: /usr/local)
        # use --name=<PATH> for custom build directory
        # use --auto-download to download and build missing, required or
        #   enabled, dependencies
    cd <build_dir>   # default is ./build
    make             # use -jN for parallel build with N threads
    make check       # to run default set of tests
    make install     # to install into the prefix specified above

All binaries are built into `<build_dir>/bin`, the cvc5 library is built into
`<build_dir>/lib`.

## Supported Operating Systems

cvc5 can be built on Linux and macOS.  Cross-compilation is possible for Arm64
systems and Windows using Mingw-w64.  We recommend a 64-bit operating system.

On macOS, we recommend using Homebrew (https://brew.sh/) to install the
dependencies.  We also have a Homebrew Tap available at
https://github.com/CVC4/homebrew-cvc4 .
To build a static binary for macOS, use:
`./configure.sh --static --no-static-binary`.

### Cross-compiling for Windows

Cross-compiling cvc5 with Mingw-w64 can be done as follows:

```
  ./configure.sh --win64 --static <configure options...>

  cd <build_dir>   # default is ./build
  make             # use -jN for parallel build with N threads
```

The built binary `cvc5.exe` is located in `<build_dir>/bin` and the cvc5 library
can be found in `<build_dir>/lib`.

## Build dependencies

cvc5 makes uses of a number of tools and libraries. Some of these are required
while others are only used with certain configuration options. If
`--auto-download` is given, cvc5 can automatically download and build most
libraries that are not already installed on your system. Versions given are
minimum versions; more recent versions should be compatible.

- [GNU C and C++ (gcc and g++)](https://gcc.gnu.org)
  or [Clang](https://clang.llvm.org) (reasonably recent versions)
- [CMake >= 3.9](https://cmake.org)
- [Python 3.x](https://www.python.org)
  + module [toml](https://pypi.org/project/toml/)
- [GMP v6.1 (GNU Multi-Precision arithmetic library)](https://gmplib.org)
- [ANTLR 3.4](http://www.antlr3.org/)
- [Java >= 1.6](https://www.java.com)


### ANTLR 3.4 parser generator

For most systems, the package manager no longer contains pre-packaged versions
of ANTLR 3.4. With `--auto-download`, cvc5 will automatically download and build
ANTLR 3.4.


### GMP (GNU Multi-Precision arithmetic library)

GMP is usually available on you distribution and should be used from there. It
can be downloaded and built automatically. If it does not, or you want to
cross-compile, or you want to build cvc5 statically but the distribution does
not ship static libraries, cvc5 builds GMP automatically when `--auto-download`
is given.

## Optional Dependencies

### SymFPU (Support for the Theory of Floating Point Numbers)

[SymFPU](https://github.com/martin-cs/symfpu/tree/CVC4)
is an implementation of SMT-LIB/IEEE-754 floating-point operations in terms
of bit-vector operations.
It is required for supporting the theory of floating-point numbers and
can be downloaded and built automatically.
Configure cvc5 with `configure.sh --symfpu` to build with this dependency.

### CaDiCaL (Optional SAT solver)

[CaDiCaL](https://github.com/arminbiere/cadical)
is a SAT solver that can be used for solving non-incremental bit-vector
problems with eager bit-blasting. This dependency may improve performance.
It can be downloaded and built automatically.
Configure cvc5 with `configure.sh --cadical` to build with this dependency.

### CryptoMiniSat (Optional SAT solver)

[CryptoMinisat](https://github.com/msoos/cryptominisat)
is a SAT solver that can be used for solving bit-vector problems with eager
bit-blasting. This dependency may improve performance.
It can be downloaded and built automatically.
Configure cvc5 with `configure.sh --cryptominisat` to build with this
dependency.

### Kissat (Optional SAT solver)

[Kissat](https://github.com/arminbiere/kissat)
is a SAT solver that can be used for solving bit-vector problems with eager
bit-blasting. This dependency may improve performance.
It can be downloaded and built automatically.
Configure cvc5 with `configure.sh --kissat` to build with this
dependency.

### LibPoly (Optional polynomial library)

[LibPoly](https://github.com/SRI-CSL/libpoly) is required for CAD-based
nonlinear reasoning. It can be downloaded and built automatically. Configure
cvc5 with `configure.sh --poly` to build with this dependency.

### CLN >= v1.3 (Class Library for Numbers)

[CLN](http://www.ginac.de/CLN)
is an alternative multiprecision arithmetic package that may offer better
performance and memory footprint than GMP.
Configure cvc5 with `configure.sh --cln` to build with this dependency.

Note that CLN is covered by the [GNU General Public License, version
3](https://www.gnu.org/licenses/gpl-3.0.en.html). If you choose to use cvc5 with
CLN support, you are licensing cvc5 under that same license. (Usually cvc5's
license is more permissive than GPL, see the file `COPYING` in the cvc5 source
distribution for details.)

### glpk-cut-log (A fork of the GNU Linear Programming Kit)

[glpk-cut-log](https://github.com/timothy-king/glpk-cut-log/) is a fork of
[GLPK](http://www.gnu.org/software/glpk/) (the GNU Linear Programming Kit).
This can be used to speed up certain classes of problems for the arithmetic
implementation in cvc5. (This is not recommended for most users.)

glpk-cut-log can be installed using the `contrib/get-glpk-cut-log` script.
Note that the only installation option is manual installation via this script.
cvc5 is no longer compatible with the main GLPK library.
Configure cvc5 with `configure.sh --glpk` to build with this dependency.

Note that GLPK and glpk-cut-log are covered by the [GNU General Public License,
version 3](https://www.gnu.org/licenses/gpl-3.0.en.html). If you choose to use
cvc5 with GLPK support, you are licensing cvc5 under that same license. (Usually
cvc5's license is more permissive; see above discussion.)

### ABC library (Improved Bit-Vector Support)

[ABC](http://www.eecs.berkeley.edu/~alanmi/abc/) (A System for Sequential
Synthesis and Verification) is a library for synthesis and verification of
logic circuits. This dependency may improve performance of the eager
bit-vector solver. When enabled, the bit-blasted formula is encoded into
and-inverter-graphs (AIG) and ABC is used to simplify these AIGs.

ABC can be installed using the `contrib/get-abc` script.
Configure cvc5 with `configure.sh --abc` to build with this dependency.

### Editline library (Improved Interactive Experience)

The [Editline Library](https://thrysoee.dk/editline/) library is optionally
used to provide command editing, tab completion, and history functionality at
the cvc5 prompt (when running in interactive mode).  Check your distribution
for a package named "libedit-dev" or "libedit-devel" or similar.

### Google Test Unit Testing Framework (Unit Tests)

[Google Test](https://github.com/google/googletest) is required to optionally
run cvc5's unit tests (included with the distribution).
See [Testing cvc5](#Testing-cvc5) below for more details.

## Language bindings

cvc5 provides a complete and flexible C++ API (see `examples/api` for
examples). It further provides Java (see `examples/SimpleVC.java` and
`examples/api/java`) and Python (see `examples/api/python`) API bindings.

Configure cvc5 with `configure.sh --<lang>-bindings` to build with language
bindings for `<lang>`.

If you're interested in helping to develop, maintain, and test a language
binding, please contact one of the project leaders.


## Building the API Documentation

Building the API documentation of cvc5 requires the following dependencies:
* [Doxygen](https://www.doxygen.nl)
* [Sphinx](https://www.sphinx-doc.org),
  [sphinx-tabs](https://sphinx-tabs.readthedocs.io/),
  [sphinxcontrib-bibtex](https://sphinxcontrib-bibtex.readthedocs.io)
* [Breathe](https://breathe.readthedocs.io)

To build the documentation, configure cvc5 with `./configure.sh --docs`.
Building cvc5 will then include building the API documentation.

The API documentation can then be found at `<build_dir>/docs/sphinx/index.html`.

To only build the documentation, change to the build directory and call
`make docs`.

To build the documentation for GitHub pages, change to the build directory
and call `make docs-gh`. The content of directory `<build_dir>/docs/sphinx-gh`
can then be copied over to GitHub pages.


## Building the Examples

See `examples/README.md` for instructions on how to build and run the examples.

## Testing cvc5

We use `ctest` as test infrastructure, for all command-line options of ctest,
see `ctest -h`. Some useful options are:

    ctest -R <regex>           # run all tests with names matching <regex>
    ctest -E <regex>           # exclude tests with names matching <regex>
    ctest -L <regex>           # run all tests with labels matching <regex>
    ctest -LE <regex>          # exclude tests with labels matching <regex>
    ctest                      # run all tests
    ctest -jN                  # run all tests in parallel with N threads
    ctest --output-on-failure  # run all tests and print output of failed tests

We have 4 categories of tests:
- **examples** in directory `examples`
  (label: **example**)
- **regression tests** (5 levels) in directory `test/regress`
  (label: **regressN** with N the regression level)
- **api tests** in directory `test/api`
  (label: **api**)
- **unit tests** in directory `test/unit`
  (label: **unit**)

### Testing System Tests

The system tests are not built by default.

    make apitests                         # build and run all system tests
    make <api_test>                       # build test/system/<system_test>.<ext>
    ctest api/<api_test>                  # run test/system/<system_test>.<ext>

All system test binaries are built into `<build_dir>/bin/test/system`.

We use prefix `api/` + `<api_test>` (for `<api_test>` in `test/api`)
as test target name.

    make ouroborous                       # build test/api/ouroborous.cpp
    ctest -R ouroborous                   # run all tests that match '*ouroborous*'
                                          # > runs api/ouroborous
    ctest -R ouroborous$                  # run all tests that match '*ouroborous'
                                          # > runs api/ouroborous
    ctest -R api/ouroborous$              # run all tests that match '*api/ouroborous'
                                          # > runs api/ouroborous
### Testing Unit Tests

The unit tests are not built by default.

Note that cvc5 can only be configured with unit tests in non-static builds with
assertions enabled.

    make units                            # build and run all unit tests
    make <unit_test>                      # build test/unit/<subdir>/<unit_test>.<ext>
    ctest unit/<subdir>/<unit_test>       # run test/unit/<subdir>/<unit_test>.<ext>

All unit test binaries are built into `<build_dir>/bin/test/unit`.

We use prefix `unit/` + `<subdir>/` + `<unit_test>` (for `<unit_test>` in
`test/unit/<subdir>`) as test target name.

    make map_util_black                   # build test/unit/base/map_util_black.cpp
    ctest -R map_util_black               # run all tests that match '*map_util_black*'
                                          # > runs unit/base/map_util_black
    ctest -R base/map_util_black$         # run all tests that match '*base/map_util_black'
                                          # > runs unit/base/map_util_black
    ctest -R unit/base/map_util_black$    # run all tests that match '*unit/base/map_util_black'
                                          # > runs unit/base/map_util_black

### Testing Regression Tests

We use prefix `regressN/` + `<subdir>/` + `<regress_test>` (for `<regress_test>`
in level `N` in `test/regress/regressN/<subdir>`) as test target name.

    ctest -L regress                      # run all regression tests
    ctest -L regress0                     # run all regression tests in level 0
    ctest -L regress[0-1]                 # run all regression tests in level 0 and 1
    ctest -R regress                      # run all regression tests
    ctest -R regress0                     # run all regression tests in level 0
    ctest -R regress[0-1]                 # run all regression tests in level 0 and 1
    ctest -R regress0/bug288b             # run all tests that match '*regress0/bug288b*'
                                          # > runs regress0/bug288b
### Custom Targets

All custom test targets build and run a preconfigured set of tests.

- `make check [-jN] [ARGS=-jN]`
  The default build-and-test target for cvc5, builds and runs all examples,
  all system and unit tests, and regression tests from levels 0 to 2.

- `make systemtests [-jN] [ARGS=-jN]`
  Build and run all system tests.

- `make units [-jN] [ARGS=-jN]`
  Build and run all unit tests.

- `make regress [-jN] [ARGS=-jN]`
  Build and run regression tests from levels 0 to 2.

- `make runexamples [-jN] [ARGS=-jN]`
  Build and run all examples.

- `make coverage [-jN] [ARGS=-jN]`
  Build and run all tests (system and unit tests, regression tests level 0-4)
  with gcov to determine code coverage.

We use `ctest` as test infrastructure, and by default all test targets
are configured to **run** in parallel with the maximum number of threads
available on the system. Override with `ARGS=-jN`.

Use `-jN` for parallel **building** with `N` threads.


## Recompiling a specific cvc5 version with different LGPL library versions

To recompile a specific static binary of cvc5 with different versions of the
linked LGPL libraries perform the following steps:

1. Make sure that you have installed the desired LGPL library versions.
   You can check the versions found by cvc5's build system during the configure
   phase.

2. Determine the commit sha and configuration of the cvc5 binary
```
cvc5 --show-config
```
3. Download the specific source code version:
```
wget https://github.com/CVC4/CVC4/archive/<commit-sha>.tar.gz
```
4. Extract the source code
```
tar xf <commit-sha>.tar.gz
```
5. Change into source code directory
```
cd cvc5-<commit-sha>
```
6. Configure cvc5 with options listed by `cvc5 --show-config`
```
./configure.sh --static <options>
```

7. Follow remaining steps from [build instructions](#building-cvc5)
