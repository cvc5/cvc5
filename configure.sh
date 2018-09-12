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
  -h, --help               display this help and exit
  --build-dir-prefix=STR   prefix build directory with given prefix
  --best                   turn on dependences known to give best performance
  --gpl                    permit GPL dependences, if available


Features:
The following flags enable optional features (disable with --no-<option name>).
  --static                 build static libraries and binaries [default=no]
  --proofs                 support for proof generation
  --optimized              optimize the build
  --debug-symbols          include debug symbols
  --valgrind               Valgrind instrumentation
  --debug-context-mm       use the debug context memory manager
  --statistics             do not include statistics
  --replay                 turn off the replay feature
  --assertions             turn off assertions
  --tracing                remove all tracing code
  --dumping                remove all dumping code
  --muzzle                 complete silence (no non-result output)
  --coverage               support for gcov coverage testing
  --profiling              support for gprof profiling
  --unit-testing           support for unit testing
  --python2                prefer using Python 2 (for Python bindings)

The following options configure parameterized features.

  --language-bindings[=java,python,all]
                          specify language bindings to build

Optional Packages:
The following flags enable optional packages (disable with --no-<option name>).
  --cln                    use CLN instead of GMP
  --gmp                    use GMP instead of CLN
  --glpk                   use GLPK simplex solver
  --abc                    use the ABC AIG library
  --cadical                use the CaDiCaL SAT solver
  --cryptominisat          use the CRYPTOMINISAT sat solver
  --lfsc                   use the LFSC proof checker
  --symfpu                 use symfpu for floating point solver
  --portfolio              build the multithreaded portfolio version of CVC4
                           (pcvc4)
  --readline               support the readline library

Optional Path to Optional Packages:
  --abc-dir=PATH           path to top level of abc source tree
  --antlr-dir=PATH         path to ANTLR C headers and libraries
  --cadical-dir=PATH       path to top level of CaDiCaL source tree
  --cryptominisat-dir=PATH path to top level of cryptominisat source tree
  --cxxtest-dir=DIR        path to CxxTest installation
  --glpk-dir=PATH          path to top level of glpk installation
  --lfsc-dir=PATH          path to top level of lfsc source tree
  --symfpu-dir=PATH        path to top level of symfpu source tree

Report bugs to <cvc4-bugs@cs.stanford.edu>.
EOF
  exit 0
}

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

builddir=default
prefix=""

#--------------------------------------------------------------------------#

buildtype=default

abc=default
asan=default
assertions=default
best=default
cadical=default
cln=default
coverage=default
cryptominisat=default
debug_symbols=default
debug_context_mm=default
dumping=default
gpl=default
glpk=default
lfsc=default
muzzle=default
optimized=default
portfolio=default
proofs=default
replay=default
shared=default
statistics=default
symfpu=default
tracing=default
unit_testing=default
python2=default
valgrind=default
profiling=default
readline=default

language_bindings_java=default
language_bindings_python=default

abc_dir=default
antlr_dir=default
cadical_dir=default
cryptominisat_dir=default
glpk_dir=default
lfsc_dir=default
symfpu_dir=default

#--------------------------------------------------------------------------#

while [ $# -gt 0 ]
do
  case $1 in

    -h|--help) usage;;

    --abc) abc=ON;;
    --no-abc) abc=OFF;;

    --asan) asan=ON;;
    --no-asan) asan=OFF;;

    --assertions) assertions=ON;;
    --no-assertions) assertions=OFF;;

    --best) best=ON;;
    --no-best) best=OFF;;

    --build-dir-prefix) die "missing argument to $1 (try -h)" ;;
    --build-dir-prefix=*) prefix=$1 ;;

    --cadical) cadical=ON;;
    --no-cadical) cadical=OFF;;

    --cln) cln=ON;;
    --no-cln) cln=OFF;;

    --coverage) coverage=ON;;
    --no-coverage) coverage=OFF;;

    --cryptominisat) cryptominisat=ON;;
    --no-cryptominisat) cryptominisat=OFF;;

    --debug-symbols) debug_symbols=ON;;
    --no-debug-symbols) debug_symbols=OFF;;

    --debug-context-memory-manager) debug_context_mm=ON;;
    --no-debug-context-memory-manager) debug_context_mm=OFF;;

    --dumping) dumping=ON;;
    --no-dumping) dumping=OFF;;

    --gpl) gpl=ON;;
    --no-gpl) gpl=OFF;;

    --glpk) glpk=ON;;
    --no-glpk) glpk=OFF;;

    --lfsc) lfsc=ON;;
    --no-lfsc) lfsc=OFF;;

    --muzzle) muzzle=ON;;
    --no-muzzle) muzzle=OFF;;

    --optimized) optimized=ON;;
    --no-optimized) optimized=OFF;;

    --portfolio) portfolio=ON;;
    --no-portfolio) portfolio=OFF;;

    --proofs) proofs=ON;;
    --no-proofs) proofs=OFF;;

    --replay) replay=ON;;
    --no-replay) replay=OFF;;

    --static) shared=OFF;;
    --no-static) shared=ON;;

    --statistics) statistics=ON;;
    --no-statistics) statistics=OFF;;

    --symfpu) symfpu=ON;;
    --no-symfpu) symfpu=OFF;;

    --tracing) tracing=ON;;
    --no-tracing) tracing=OFF;;

    --unit-testing) unit_testing=ON;;
    --no-unit-testing) unit_testing=OFF;;

    --python2) python2=ON;;
    --no-python2) python2=OFF;;

    --valgrind) valgrind=ON;;
    --no-valgrind) valgrind=OFF;;

    --profiling) profiling=ON;;
    --no-profiling) profiling=OFF;;

    --readline) readline=ON;;
    --no-readline) readline=OFF;;

    --language-bindings) die "missing argument to $1 (try -h)" ;;
    --language-bindings=*)
      lang="${1##*=}"
      [[ "java python all" =~ (^|[[:space:]])"$lang"($|[[:space:]]) ]] \
        || die "invalid argument to --language-bindings (try -h)"
      if [ $lang = "java" -o $lang = "all" ]
      then
        language_bindings_java=ON
      fi
      if [ $lang = "python" -o $lang = "all" ]
      then
        language_bindings_python=ON
      fi
      ;;

    --abc-dir) die "missing argument to $1 (try -h)" ;;
    --abc-dir=*) abc_dir=${1##*=} ;;

    --antlr-dir) die "missing argument to $1 (try -h)" ;;
    --antlr-dir=*) antlr_dir=${1##*=} ;;

    --cadical-dir) die "missing argument to $1 (try -h)" ;;
    --cadical-dir=*) cadical_dir=${1##*=} ;;

    --cryptominisat-dir) die "missing argument to $1 (try -h)" ;;
    --cryptominisat-dir=*) cryptominisat_dir=${1##*=} ;;

    --glpk-dir) die "missing argument to $1 (try -h)" ;;
    --glpk-dir=*) glpk_dir=${1##*=} ;;

    --lfsc-dir) die "missing argument to $1 (try -h)" ;;
    --lfsc-dir=*) lfsc_dir=${1##*=} ;;

    --symfpu-dir) die "missing argument to $1 (try -h)" ;;
    --symfpu-dir=*) symfpu_dir=${1##*=} ;;

    -*) die "invalid option '$1' (try -h)";;

    *) case $1 in
         production)  buildtype=Production; builddir=production;;
         debug)       buildtype=Debug; builddir=debug;;
         testing)     buildtype=Testing; builddir=testing;;
         competition) buildtype=Competition; builddir=competition;;
         *)           die "invalid build type (try -h)";;
       esac
       ;;
  esac
  shift
done

builddir="$prefix$builddir"

#--------------------------------------------------------------------------#

cmake_opts=""

[ $buildtype != default ] && cmake_opts="$cmake_opts -DCMAKE_BUILD_TYPE=$buildtype"

[ $asan != default ] \
  && cmake_opts="$cmake_opts -DENABLE_ASAN=$asan" \
  && [ $asan = ON ] && builddir="$builddir-asan"
[ $assertions != default ] \
  && cmake_opts="$cmake_opts -DENABLE_ASSERTIONS=$assertions" \
  && [ $assertions = ON ] && builddir="$builddir-assertions"
[ $best != default ] \
  && cmake_opts="$cmake_opts -DENABLE_BEST=$best" \
  && [ $best = ON ] && builddir="$builddir-best"
[ $coverage != default ] \
  && cmake_opts="$cmake_opts -DENABLE_COVERAGE=$coverage" \
  && [ $coverage = ON ] && builddir="$builddir-coverage"
[ $debug_symbols != default ] \
  && cmake_opts="$cmake_opts -DENABLE_DEBUG_SYMBOLS=$debug_symbols" \
  && [ $debug_symbols = ON ] && builddir="$builddir-debug_symbols"
[ $debug_context_mm != default ] \
  && cmake_opts="$cmake_opts -DENABLE_DEBUG_CONTEXT_MM=$debug_context_mm" \
  && [ $debug_context_mm = ON ] &&  builddir="$builddir-debug_context_mm"
[ $dumping != default ] \
  && cmake_opts="$cmake_opts -DENABLE_DUMPING=$dumping" \
  && [ $dumping = ON ] &&  builddir="$builddir-dumping"
[ $gpl != default ] \
  && cmake_opts="$cmake_opts -DENABLE_GPL=$gpl" \
  && [ $gpl = ON ] &&  builddir="$builddir-gpl"
[ $muzzle != default ] \
  && cmake_opts="$cmake_opts -DENABLE_MUZZLE=$muzzle" \
  && [ $muzzle = ON ] &&  builddir="$builddir-muzzle"
[ $optimized != default ] \
  && cmake_opts="$cmake_opts -DENABLE_OPTIMIZED=$optimized" \
  && [ $optimized = ON ] &&  builddir="$builddir-optimized"
[ $portfolio != default ] \
  && cmake_opts="$cmake_opts -DENABLE_PORTFOLIO=$portfolio" \
  && [ $portfolio = ON ] &&  builddir="$builddir-portfolio"
[ $proofs != default ] \
  && cmake_opts="$cmake_opts -DENABLE_PROOFS=$proofs" \
  && [ $proofs = ON ] &&  builddir="$builddir-proofs"
[ $replay != default ] \
  && cmake_opts="$cmake_opts -DENABLE_REPLAY=$replay" \
  && [ $replay = ON ] &&  builddir="$builddir-replay"
[ $shared != default ] \
  && cmake_opts="$cmake_opts -DENABLE_STATIC=$shared" \
  && [ $shared == OFF ] &&  builddir="$builddir-static"
[ $statistics != default ] \
  && cmake_opts="$cmake_opts -DENABLE_STATISTICS=$statistics" \
  && [ $statistics = ON ] && builddir="$builddir-stastitics"
[ $tracing != default ] \
  && cmake_opts="$cmake_opts -DENABLE_TRACING=$tracing" \
  && [ $tracing = ON ] && builddir="$builddir-tracing"
[ $unit_testing != default ] \
  && cmake_opts="$cmake_opts -DENABLE_UNIT_TESTING=$unit_testing" \
  && [ $unit_testing = ON ] && builddir="$builddir-unit_testing"
[ $python2 != default ] \
  && cmake_opts="$cmake_opts -DUSE_PYTHON2=$python2" \
  && [ $python2 = ON ] && builddir="$builddir-python2"
[ $valgrind != default ] \
  && cmake_opts="$cmake_opts -DENABLE_VALGRIND=$valgrind" \
  && [ $valgrind = ON ] && builddir="$builddir-valgrind"
[ $profiling != default ] \
  && cmake_opts="$cmake_opts -DENABLE_PROFILING=$profiling" \
  && [ $profiling = ON ] && builddir="$builddir-profiling"
[ $readline != default ] \
  && cmake_opts="$cmake_opts -DENABLE_READLINE=$readline" \
  && [ $readline = ON ] && builddir="$builddir-readline"
[ $abc != default ] \
  && cmake_opts="$cmake_opts -DUSE_ABC=$abc" \
  && [ $abc = ON ] && builddir="$builddir-abc"
[ $cadical != default ] \
  && cmake_opts="$cmake_opts -DUSE_CADICAL=$cadical" \
  && [ $cadical = ON ] && builddir="$builddir-cadical"
[ $cln != default ] \
  && cmake_opts="$cmake_opts -DUSE_CLN=$cln" \
  && [ $cln = ON ] && builddir="$builddir-cln"
[ $cryptominisat != default ] \
  && cmake_opts="$cmake_opts -DUSE_CRYPTOMINISAT=$cryptominisat" \
  && [ $cryptominisat = ON ] && builddir="$builddir-cryptominisat"
[ $glpk != default ] \
  && cmake_opts="$cmake_opts -DUSE_GLPK=$glpk" \
  && [ $glpk = ON ] && builddir="$builddir-glpk"
[ $lfsc != default ] \
  && cmake_opts="$cmake_opts -DUSE_LFSC=$lfsc" \
  && [ $lfsc = ON ] && builddir="$builddir-lfsc"
[ $symfpu != default ] \
  && cmake_opts="$cmake_opts -DUSE_SYMFPU=$symfpu" \
  && [ $symfpu = ON ] && builddir="$builddir-symfpu"

[ $language_bindings_java != default ] \
  && cmake_opts="$cmake_opts -DBUILD_BINDINGS_JAVA=$language_bindings_java"
[ $language_bindings_python != default ] \
  && cmake_opts="$cmake_opts -DBUILD_BINDINGS_PYTHON=$language_bindings_python"

[ $abc_dir != default ] \
  && cmake_opts="$cmake_opts -DABC_DIR=$abc_dir"
[ $antlr_dir != default ] \
  && cmake_opts="$cmake_opts -DANTLR_DIR=$antlr_dir"
[ $cadical_dir != default ] \
  && cmake_opts="$cmake_opts -DCADICAL_DIR=$cadical_dir"
[ $cryptominisat_dir != default ] \
  && cmake_opts="$cmake_opts -DCRYPTOMINISAT_DIR=$cryptominisat_dir"
[ $glpk_dir != default ] \
  && cmake_opts="$cmake_opts -DGLPK_DIR=$glpk_dir"
[ $lfsc_dir != default ] \
  && cmake_opts="$cmake_opts -DLFSC_DIR=$lfsc_dir"
[ $symfpu_dir != default ] \
  && cmake_opts="$cmake_opts -DSYMFPU_DIR=$symfpu_dir"

mkdir -p cmake-builds  # builds parent directory
cd cmake-builds
ln -sf $builddir build  # link to current build directory
mkdir -p $builddir     # current build directory
cd $builddir

[ -e CMakeCache.txt ] && rm CMakeCache.txt
cmake ../.. $cmake_opts
