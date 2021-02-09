CVC4 prerelease version 1.9
===========================

## Building CVC4

    ./contrib/get-antlr-3.4  # download and build ANTLR
    ./configure.sh   # use --prefix to specify a prefix (default: /usr/local)
                     # use --name=<PATH> for custom build directory
    cd <build_dir>   # default is ./build
    make             # use -jN for parallel build with N threads
    make check       # to run default set of tests
    make install     # to install into the prefix specified above

All binaries are built into `<build_dir>/bin`, the CVC4 library is built into
`<build_dir>/lib`.

## Supported Operating Systems

CVC4 can be built on Linux and macOS.  For Windows, CVC4 can be cross-compiled
using Mingw-w64.  We recommend a 64-bit operating system.

On macOS, we recommend using Homebrew (https://brew.sh/) to install the
dependencies.  We also have a Homebrew Tap available at
https://github.com/CVC4/homebrew-cvc4 .
To build a static binary for macOS, use:
`./configure.sh --static --no-static-binary`.

### Cross-compiling for Windows

Cross-compiling CVC4 with Mingw-w64 can be done as follows:

```
  HOST=x86_64-w64-mingw32 ./contrib/get-win-dependencies
  ./configure.sh --win64 --static <configure options...>

  cd <build_dir>   # default is ./build
  make             # use -jN for parallel build with N threads
```

The built binary `cvc4.exe` is located in `<build_dir>/bin` and the CVC4 library
can be found in `<build_dir>/lib`.

## Build dependencies

The following tools and libraries are required to build and run CVC4.  
Versions given are minimum versions; more recent versions should be
compatible.

- [GNU C and C++ (gcc and g++)](https://gcc.gnu.org)
  or [Clang](https://clang.llvm.org) (reasonably recent versions)
- [CMake >= 3.9](https://cmake.org)
- [GNU Bash](https://www.gnu.org/software/bash/)
- [Python >= 2.7](https://www.python.org)
  + module [toml](https://pypi.org/project/toml/)
- [GMP v4.2 (GNU Multi-Precision arithmetic library)](https://gmplib.org)
- [libantlr3c v3.2 or v3.4 (ANTLR parser generator C support library)](http://www.antlr3.org/)
- [Java >= 1.6](https://www.java.com)

Some features, such as the theory of floating-point numbers, require
[optional dependencies](optional-dependencies) (see below).

### Installing libantlr3c: ANTLR parser generator C support library

For libantlr3c, you can use the script `contrib/get-antlr-3.4`.
This will download, patch, and install libantlr3c.

If you're on a 32-bit machine, or if you have difficulty building
libantlr3c (or difficulty getting CVC4 to link against it), you
may need to remove the configure option `--enable-64bit` in the script.

### Warning: GCC 4.5.1

GCC version 4.5.1 seems to have a bug in the optimizer that may result in
incorrect behavior (and wrong results) in many builds. This is a known problem
for MiniSat, and since MiniSat is at the core of CVC4, a problem for CVC4.
We recommend using a GCC version > 4.5.1.

### Warning: Installing GMP via `contrib/get-gmp-dev`

Do **not** install GMP via the provided script `contrib/get-gmp-dev` unless
your distribution
* does not ship with the GMP configuration you need, e.g.,
  script `contrib/get-win-dependencies` uses `contrib/get-gmp-dev` when
  cross-compiling GMP for Windows.
* does not ship with static GMP libraries (e.g., Arch Linux)
  and you want to build CVC4 statically.

In most of the cases the GMP version installed on your system is the one you
want and should use.

## Optional Dependencies

### SymFPU (Support for the Theory of Floating Point Numbers)

[SymFPU](https://github.com/martin-cs/symfpu/tree/CVC4)
is an implementation of SMT-LIB/IEEE-754 floating-point operations in terms
of bit-vector operations.
It is required for supporting the theory of floating-point numbers and
can be installed using the `contrib/get-symfpu` script.  
Configure CVC4 with `configure.sh --symfpu` to build with this dependency.

### CaDiCaL (Optional SAT solver)

[CaDiCaL](https://github.com/arminbiere/cadical)
is a SAT solver that can be used for solving non-incremental bit-vector
problems with eager bit-blasting. This dependency may improve performance.
It can be installed using the `contrib/get-cadical script`.  
Configure CVC4 with `configure.sh --cadical` to build with this dependency.

### CryptoMiniSat (Optional SAT solver)

[CryptoMinisat](https://github.com/msoos/cryptominisat)
is a SAT solver that can be used for solving bit-vector problems with eager
bit-blasting. This dependency may improve performance.
It can be installed using the `contrib/get-cryptominisat` script.  
Configure CVC4 with `configure.sh --cryptominisat` to build with this
dependency.

### Kissat (Optional SAT solver)

[Kissat](https://github.com/arminbiere/kissat)
is a SAT solver that can be used for solving bit-vector problems with eager
bit-blasting. This dependency may improve performance.
It can be installed using the `contrib/get-kissat` script.  
Configure CVC4 with `configure.sh --kissat` to build with this
dependency.

### LFSC (The LFSC Proof Checker)

[LFSC](https://github.com/CVC4/LFSC) is required to check proofs internally
with --check-proofs. It can be installed using the `contrib/get-lfsc` script.  
Configure CVC4 with `configure.sh --lfsc` to build with this dependency.

### LibPoly (Optional polynomial library)

[LibPoly](https://github.com/SRI-CSL/libpoly) is required for CAD-based nonlinear reasoning.
It can be installed using the `contrib/get-poly` script.
Configure CVC4 with `configure.sh --poly` to build with this dependency.

### CLN >= v1.3 (Class Library for Numbers)

[CLN](http://www.ginac.de/CLN)
is an alternative multiprecision arithmetic package that may offer better
performance and memory footprint than GMP.  
Configure CVC4 with `configure.sh --cln` to build with this dependency.

Note that CLN is covered by the [GNU General Public License, version 3](https://www.gnu.org/licenses/gpl-3.0.en.html).
If you choose to use CVC4 with CLN support, you are licensing CVC4 under that
same license.
(Usually CVC4's license is more permissive than GPL, see the file `COPYING` in
the CVC4 source distribution for details.)

### glpk-cut-log (A fork of the GNU Linear Programming Kit)

[glpk-cut-log](https://github.com/timothy-king/glpk-cut-log/) is a fork of
[GLPK](http://www.gnu.org/software/glpk/) (the GNU Linear Programming Kit).
This can be used to speed up certain classes of problems for the arithmetic
implementation in CVC4. (This is not recommended for most users.)

glpk-cut-log can be installed using the `contrib/get-glpk-cut-log` script.
Note that the only installation option is manual installation via this script.
CVC4 is no longer compatible with the main GLPK library.  
Configure CVC4 with `configure.sh --glpk` to build with this dependency.

Note that GLPK and glpk-cut-log are covered by the [GNU General Public License, version 3](https://www.gnu.org/licenses/gpl-3.0.en.html).
If you choose to use CVC4 with GLPK support, you are licensing CVC4 under that
same license.
(Usually CVC4's license is more permissive; see above discussion.)

### ABC library (Improved Bit-Vector Support)

[ABC](http://www.eecs.berkeley.edu/~alanmi/abc/) (A System for Sequential
Synthesis and Verification) is a library for synthesis and verification of
logic circuits. This dependency may improve performance of the eager
bit-vector solver. When enabled, the bit-blasted formula is encoded into
and-inverter-graphs (AIG) and ABC is used to simplify these AIGs.

ABC can be installed using the `contrib/get-abc` script.  
Configure CVC4 with `configure.sh --abc` to build with this dependency.

### Editline library (Improved Interactive Experience)

The [Editline Library](https://thrysoee.dk/editline/) library is optionally
used to provide command editing, tab completion, and history functionality at
the CVC4 prompt (when running in interactive mode).  Check your distribution
for a package named "libedit-dev" or "libedit-devel" or similar.

### Boost C++ base libraries (Examples)

The [Boost](http://www.boost.org) C++ base library is needed for some examples
provided with CVC4.

### CxxTest Unit Testing Framework (Unit Tests)

[CxxTest](http://cxxtest.com) is required to optionally run CVC4's unit tests
(included with the distribution). 
See [Testing CVC4](#Testing-CVC4) below for more details.


### Google Test Unit Testing Framework (Unit Tests)

[Google Test](https://github.com/google/googletest) is required to optionally
run CVC4's unit tests (included with the distribution). 
See [Testing CVC4](#Testing-CVC4) below for more details.

## Language bindings

CVC4 provides a complete and flexible C++ API (see `examples/api` for
examples). It further provides Java (see `examples/SimpleVC.java` and
`examples/api/java`) and Python (see `examples/api/python`) API bindings.

Configure CVC4 with `configure.sh --<lang>-bindings` to build with language
bindings for `<lang>`.

If you're interested in helping to develop, maintain, and test a language
binding, please contact one of the project leaders.

## Building the Examples

See `examples/README.md` for instructions on how to build and run the examples.

## Testing CVC4

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

Note that CVC4 can only be configured with unit tests in non-static builds with
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
  The default build-and-test target for CVC4, builds and runs all examples,
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


## Recompiling a specific CVC4 version with different LGPL library versions

To recompile a specific static binary of CVC4 with different versions of the
linked LGPL libraries perform the following steps:

1. Make sure that you have installed the desired LGPL library versions.
   You can check the versions found by CVC4's build system during the configure
   phase.

2. Determine the commit sha and configuration of the CVC4 binary
```
cvc4 --show-config
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
cd CVC4-<commit-sha>
```
6. Configure CVC4 with options listed by `cvc4 --show-config`
```
./configure.sh --static <options>
```

7. Follow remaining steps from [build instructions](#building-cvc4)
