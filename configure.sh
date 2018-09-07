#!/bin/sh
#--------------------------------------------------------------------------#

usage () {
cat <<EOF
Usage: VAR=VALUE $0 [<build type>] [<option> ...]

Build types:
  production
  debug
  testing
  competition


General options;
  -h, --help              display this help and exit

  --gpl                   permit GPL dependences, if available
  --best                  turn on dependences known to give best performance


Features:

The following flags enable optional features (disable with --no-<option name>).

  --static                build static libraries and binaries [default=no]

  --proofs                support for proof generation
  --optimized             optimize the build
  --debug-symbols         include debug symbols
  --valgrind              Valgrind instrumentation
  --debug-context-memory-manager
                          use the debug context memory manager
  --statistics            do not include statistics
  --replay                turn off the replay feature
  --assertions            turn off assertions
  --tracing               remove all tracing code
  --dumping               remove all dumping code
  --muzzle                complete silence (no non-result output)
  --coverage              support for gcov coverage testing
  --profiling             support for gprof profiling
  --unit-testing          support for unit testing
  --thread-support        support for multithreaded-capable library

The following options configure parameterized features.

  --language-bindings[=c,c++,java,all]
                          specify language bindings to build

Optional Packages:

  --cln                   use CLN instead of GMP
  --gmp                   use GMP instead of CLN
  --glpk                  use GLPK simplex solver
  --glpk-dir=PATH         path to top level of glpk installation
  --abc                   use the ABC AIG library
  --abc-dir=PATH          path to top level of abc source tree
  --cadical               use the CaDiCaL SAT solver
  --cadical-dir=PATH      path to top level of CaDiCaL source tree
  --cryptominisat         use the CRYPTOMINISAT sat solver
  --cryptominisat-dir=PATH
                          path to top level of cryptominisat source tree
  --lfsc                  use the LFSC proof checker
  --lfsc-dir=PATH         path to top level of lfsc source tree
  --symfpu                use symfpu for floating point solver
  --symfpu-dir=PATH       path to top level of symfpu source tree
  --cxxtest-dir=DIR       path to CxxTest installation
  --antlr-dir=PATH        path to ANTLR C headers and libraries
  --swig=BINARY           path to swig binary
  --boost=DIR             prefix of Boost [guess]
  --portfolio             build the multithreaded portfolio version of CVC4
                          (pcvc4)
  --readline              support the readline library

Report bugs to <cvc4-bugs@cs.stanford.edu>.
EOF
  exit 0
}

#To assign environment variables (e.g., CC, CFLAGS...), specify them as
#VAR=VALUE.  See below for descriptions of some of the useful variables.
#
#Some influential environment variables:
#  CXX         C++ compiler command
#  CXXFLAGS    C++ compiler flags
#  LDFLAGS     linker flags, e.g. -L<lib dir> if you have libraries in a
#              nonstandard directory <lib dir>
#  LIBS        libraries to pass to the linker, e.g. -l<library>
#  CPPFLAGS    (Objective) C/C++ preprocessor flags, e.g. -I<include dir> if
#              you have headers in a nonstandard directory <include dir>
#  CC          C compiler command
#  CFLAGS      C compiler flags
#  LT_SYS_LIBRARY_PATH
#              User-defined run-time library search path.
#  CPP         C preprocessor
#  CXXCPP      C++ preprocessor
#  PKG_CONFIG  path to pkg-config utility
#  CLN_CFLAGS  C compiler flags for CLN, overriding pkg-config
#  CLN_LIBS    linker flags for CLN, overriding pkg-config
#  GLPK_HOME   path to top level of glpk installation
#  ABC_HOME    path to top level of abc source tree
#  CADICAL_HOME
#              path to top level of CaDiCaL source tree
#  CRYPTOMINISAT_HOME
#              path to top level of cryptominisat source tree
#  LFSC_HOME   path to top level of LFSC source tree
#  SYMFPU_HOME path to top level of symfpu source tree
#  ANTLR       location of the antlr3 script
#  DOXYGEN_PAPER_SIZE
#              a4wide (default), a4, letter, legal or executive
#  CXXTEST     path to CxxTest installation
#  TEST_CPPFLAGS
#              CPPFLAGS to use when testing (default=$CPPFLAGS)
#  TEST_CXXFLAGS
#              CXXFLAGS to use when testing (default=$CXXFLAGS)
#  TEST_LDFLAGS
#              LDFLAGS to use when testing (default=$LDFLAGS)
#  PERL        PERL interpreter (used when testing)
#  PYTHON      the Python interpreter
#  ANTLR_HOME  path to libantlr3c installation
#  SWIG        SWIG binary (used to generate language bindings)
#  JAVA_CPPFLAGS
#              flags to pass to compiler when building Java bindings
#  CSHARP_CPPFLAGS
#              flags to pass to compiler when building C# bindings
#  PERL_CPPFLAGS
#              flags to pass to compiler when building perl bindings
#  PHP_CPPFLAGS
#              flags to pass to compiler when building PHP bindings
#  PYTHON_INCLUDE
#              Include flags for python, bypassing python-config
#  PYTHON_CONFIG
#              Path to python-config
#  RUBY_CPPFLAGS
#              flags to pass to compiler when building ruby bindings
#  TCL_CPPFLAGS
#              flags to pass to compiler when building tcl bindings
#  OCAMLC      OCaml compiler
#  OCAMLMKTOP  OCaml runtime-maker
#  OCAMLFIND   OCaml-find binary
#  CAMLP4O     camlp4o binary
#  BOOST_ROOT  Location of Boost installation
#  JAVA        Java interpreter (used when testing Java interface)
#  JAVAC       Java compiler (used when building and testing Java interface)
#  JAVAH       Java compiler (used when building and testing Java interface)
#  JAR         Jar archiver (used when building Java interface)
#
#Use these variables to override the choices made by `configure' or to help
#it to find libraries and programs with nonstandard names/locations.


#--------------------------------------------------------------------------#

die () {
  echo "*** configure.sh: $*" 1>&2
  exit 1
}

msg () {
  echo "[configure.sh] $*"
}

#--------------------------------------------------------------------------#

[ ! -e src/theory ] && die "$0 not called from CVC4 base directory"

#--------------------------------------------------------------------------#

BUILDDIR=build

#--------------------------------------------------------------------------#

buildtype=production

abc=no
asan=no
assertions=no
best=no
bsd=no
cadical=no
cln=no
coverage=no
cryptominisat=no
debug_symbols=no
debug_context_mm=no
dumping=no
gpl=no
glpk=no
glpk_dir=no
language_bindings=no
lfsc=no
muzzle=no
optimized=no
portfolio=no
proofs=no
replay=no
static=no
statistics=no
symfpu=no
tracing=no
unit_testing=no
valgrind=no
profiling=no
readline=no
thread_support=no

abc_dir=default
antlr_dir=default
cadical_dir=default
cryptominisat_dir=default
cxxtest_dir=default
lfsc_dir=default
symfpu_dir=default

#--------------------------------------------------------------------------#

while [ $# -gt 0 ]
do
  case $1 in
    --abc) abc=yes;;
    --asan) asan=yes;;
    --assertions) assertions=yes;;
    --best) best=yes;;
    --cadical) cadical=yes;;
    --cln) cln=yes;;
    --coverage) coverage=yes;;
    --cryptominisat) cryptominisat=yes;;
    --debug-symbols) debug_symbols;;
    --debug-context-memory-manager) debug_context_mm=yes;;
    --dumping) dumping=yes;;
    --gpl) gpl=yes;;
    --glpk) glpk=yes;;
    -h|--help) usage;;
    --lfsc) lfsc=yes;;
    --muzzle) muzzle=yes;;
    --optimized) optimized=yes;;
    --portfolio) portfolio=yes;;
    --proofs) proofs=yes;;
    --replay) replay=yes;;
    --static) static=yes;;
    --statistics) statistics=yes;;
    --symfpu) symfpu=yes;;
    --tracing) tracing=yes;;
    --unit-testing) unit_testing=yes;;
    --valgrind) valgrind=yes;;
    --profiling) profiling=yes;;
    --readline) readline=yes;;
    --thread-support) thread_support=yes;;

    --language-bindings)
      shift
      if [ $# -eq 0 ]
      then
        die "missing argument to --language-bindings-dir"
      fi
      [[ "c c++ java all" =~ (^|[[:space:]])"$1"($|[[:space:]]) ]] \
        || die "invalid argument to --language-bindings (try '-h')"
      language_bindings=$1
      ;;

    --abc-dir)
      shift
      if [ $# -eq 0 ]
      then
        die "missing argument to --abc-dir"
      fi
      abc_dir=$1
      ;;
    --antlr-dir)
      shift
      if [ $# -eq 0 ]
      then
        die "missing argument to --antlr-dir"
      fi
      antlr_dir=$1
      ;;
    --cadical-dir)
      shift
      if [ $# -eq 0 ]
      then
        die "missing argument to --cadical-dir"
      fi
      cadical_dir=$1
      ;;
    --cryptominisat-dir)
      shift
      if [ $# -eq 0 ]
      then
        die "missing argument to --cryptominisat-dir"
      fi
      cryptominisat_dir=$1
      ;;
    --cxxtest-dir)
      shift
      if [ $# -eq 0 ]
      then
        die "missing argument to --cxxtest-dir"
      fi
      cxxtest_dir=$1
      ;;
    --glpk-dir)
      shift
      if [ $# -eq 0 ]
      then
        die "missing argument to --glpk-dir"
      fi
      glpk_dir=$1
      ;;
    --lfsc-dir)
      shift
      if [ $# -eq 0 ]
      then
        die "missing argument to --lfsc-dir"
      fi
      lfsc_dir=$1
      ;;
    --symfpu-dir)
      shift
      if [ $# -eq 0 ]
      then
        die "missing argument to --symfpu-dir"
      fi
      symfpu_dir=$1
      ;;

    -*) die "invalid option '$1' (try '-h')";;

    *) [[ "production debug testing competition" =~ (^|[[:space:]])"$1"($|[[:space:]]) ]] \
        || die "invalid build type (try '-h')"
       buildtype=$1
       ;;
  esac
  shift
done
