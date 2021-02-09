#!/bin/bash
#--------------------------------------------------------------------------#

set -e -o pipefail

usage () {
cat <<EOF
Usage: $0 [<build type>] [<option> ...]

Build types:
  production
  debug
  testing
  competition
  competition-inc


General options;
  -h, --help               display this help and exit
  --prefix=STR             install directory
  --program-prefix=STR     prefix of binaries prepended on make install
  --name=STR               use custom build directory name (optionally: +path)
  --best                   turn on dependencies known to give best performance
  --gpl                    permit GPL dependencies, if available
  --win64                  cross-compile for Windows 64 bit
  --ninja                  use Ninja build system


Features:
The following flags enable optional features (disable with --no-<option name>).
  --static                 build static libraries and binaries [default=no]
  --static-binary          statically link against system libraries
                           (must be disabled for static macOS builds) [default=yes]
  --proofs                 support for proof generation
  --optimized              optimize the build
  --debug-symbols          include debug symbols
  --valgrind               Valgrind instrumentation
  --debug-context-mm       use the debug context memory manager
  --statistics             include statistics
  --assertions             turn on assertions
  --tracing                include tracing code
  --dumping                include dumping code
  --muzzle                 complete silence (no non-result output)
  --coverage               support for gcov coverage testing
  --profiling              support for gprof profiling
  --unit-testing           support for unit testing
  --python2                prefer using Python 2 (also for Python bindings)
  --python3                prefer using Python 3 (also for Python bindings)
  --python-bindings        build Python bindings based on new C++ API
  --java-bindings          build Java bindings based on new C++ API
  --all-bindings           build bindings for all supported languages
  --asan                   build with ASan instrumentation
  --ubsan                  build with UBSan instrumentation
  --tsan                   build with TSan instrumentation

Optional Packages:
The following flags enable optional packages (disable with --no-<option name>).
  --cln                    use CLN instead of GMP
  --glpk                   use GLPK simplex solver
  --abc                    use the ABC AIG library
  --cadical                use the CaDiCaL SAT solver
  --cryptominisat          use the CryptoMiniSat SAT solver
  --drat2er                use drat2er (required for eager BV proofs)
  --kissat                 use the Kissat SAT solver
  --lfsc                   use the LFSC proof checker
  --poly                   use the LibPoly library
  --symfpu                 use SymFPU for floating point solver
  --editline               support the editline library

Optional Path to Optional Packages:
  --abc-dir=PATH           path to top level of ABC source tree
  --antlr-dir=PATH         path to ANTLR C headers and libraries
  --cadical-dir=PATH       path to top level of CaDiCaL source tree
  --cryptominisat-dir=PATH path to top level of CryptoMiniSat source tree
  --drat2er-dir=PATH       path to the top level of the drat2er installation
  --cxxtest-dir=PATH       path to CxxTest installation
  --glpk-dir=PATH          path to top level of GLPK installation
  --gmp-dir=PATH           path to top level of GMP installation
  --kissat-dir=PATH        path to top level of Kissat source tree
  --lfsc-dir=PATH          path to top level of LFSC source tree
  --poly-dir=PATH          path to top level of LibPoly source tree
  --symfpu-dir=PATH        path to top level of SymFPU source tree

Build limitations:
  --lib-only               only build the library, but not the executable or
                           the parser (default: off)

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

build_dir=build
install_prefix=default
program_prefix=""

#--------------------------------------------------------------------------#

buildtype=default

abc=default
asan=default
assertions=default
best=default
cadical=default
cln=default
comp_inc=default
coverage=default
cryptominisat=default
debug_context_mm=default
debug_symbols=default
drat2er=default
dumping=default
glpk=default
gpl=default
kissat=default
lfsc=default
poly=default
muzzle=default
ninja=default
optimized=default
profiling=default
proofs=default
python2=default
python3=default
python_bindings=default
java_bindings=default
editline=default
shared=default
static_binary=default
statistics=default
symfpu=default
tracing=default
tsan=default
ubsan=default
unit_testing=default
valgrind=default
win64=default

abc_dir=default
antlr_dir=default
cadical_dir=default
cryptominisat_dir=default
drat2er_dir=default
cxxtest_dir=default
glpk_dir=default
gmp_dir=default
kissat_dir=default
lfsc_dir=default
poly_dir=default
symfpu_dir=default

lib_only=default

#--------------------------------------------------------------------------#

while [ $# -gt 0 ]
do
  case $1 in

    -h|--help) usage;;

    --abc) abc=ON;;
    --no-abc) abc=OFF;;

    --asan) asan=ON;;
    --no-asan) asan=OFF;;

    --ubsan) ubsan=ON;;
    --no-ubsan) ubsan=OFF;;

    --tsan) tsan=ON;;
    --no-tsan) tsan=OFF;;

    --assertions) assertions=ON;;
    --no-assertions) assertions=OFF;;

    --best) best=ON;;
    --no-best) best=OFF;;

    --prefix) die "missing argument to $1 (try -h)" ;;
    --prefix=*)
        install_prefix=${1##*=}
        # Check if install_prefix is an absolute path and if not, make it
        # absolute.
        case $install_prefix in
          /*) ;;                                      # absolute path
          *) install_prefix=$(pwd)/$install_prefix ;; # make absolute path
        esac
        ;;

    --program-prefix) die "missing argument to $1 (try -h)" ;;
    --program-prefix=*) program_prefix=${1##*=} ;;

    --name) die "missing argument to $1 (try -h)" ;;
    --name=*) build_dir=${1##*=} ;;

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

    --debug-context-mm) debug_context_mm=ON;;
    --no-debug-context-mm) debug_context_mm=OFF;;

    --drat2er) drat2er=ON;;
    --no-drat2er) drat2er=OFF;;

    --dumping) dumping=ON;;
    --no-dumping) dumping=OFF;;

    --gpl) gpl=ON;;
    --no-gpl) gpl=OFF;;

    --kissat) kissat=ON;;
    --no-kissat) kissat=OFF;;

    --win64) win64=ON;;
    --no-win64) win64=OFF;;

    --ninja) ninja=ON;;

    --glpk) glpk=ON;;
    --no-glpk) glpk=OFF;;

    --lfsc) lfsc=ON;;
    --no-lfsc) lfsc=OFF;;

    --poly) poly=ON;;
    --no-poly) poly=OFF;;

    --muzzle) muzzle=ON;;
    --no-muzzle) muzzle=OFF;;

    --optimized) optimized=ON;;
    --no-optimized) optimized=OFF;;

    --proofs) proofs=ON;;
    --no-proofs) proofs=OFF;;

    --static) shared=OFF; static_binary=ON;;
    --no-static) shared=ON;;

    --static-binary) static_binary=ON;;
    --no-static-binary) static_binary=OFF;;

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

    --python3) python3=ON;;
    --no-python3) python3=OFF;;

    --python-bindings) python_bindings=ON;;
    --no-python-bindings) python_bindings=OFF;;

    --java-bindings) java_bindings=ON;;
    --no-java-bindings) java_bindings=OFF;;

    --all-bindings) python_bindings=ON;;

    --valgrind) valgrind=ON;;
    --no-valgrind) valgrind=OFF;;

    --profiling) profiling=ON;;
    --no-profiling) profiling=OFF;;

    --editline) editline=ON;;
    --no-editline) editline=OFF;;

    --abc-dir) die "missing argument to $1 (try -h)" ;;
    --abc-dir=*) abc_dir=${1##*=} ;;

    --antlr-dir) die "missing argument to $1 (try -h)" ;;
    --antlr-dir=*) antlr_dir=${1##*=} ;;

    --cadical-dir) die "missing argument to $1 (try -h)" ;;
    --cadical-dir=*) cadical_dir=${1##*=} ;;

    --cryptominisat-dir) die "missing argument to $1 (try -h)" ;;
    --cryptominisat-dir=*) cryptominisat_dir=${1##*=} ;;

    --cxxtest-dir) die "missing argument to $1 (try -h)" ;;
    --cxxtest-dir=*) cxxtest_dir=${1##*=} ;;

    --drat2er-dir) die "missing argument to $1 (try -h)" ;;
    --drat2er-dir=*) drat2er_dir=${1##*=} ;;

    --glpk-dir) die "missing argument to $1 (try -h)" ;;
    --glpk-dir=*) glpk_dir=${1##*=} ;;

    --gmp-dir) die "missing argument to $1 (try -h)" ;;
    --gmp-dir=*) gmp_dir=${1##*=} ;;

    --kissat-dir) die "missing argument to $1 (try -h)" ;;
    --kissat-dir=*) kissat_dir=${1##*=} ;;

    --lfsc-dir) die "missing argument to $1 (try -h)" ;;
    --lfsc-dir=*) lfsc_dir=${1##*=} ;;

    --poly-dir) die "missing argument to $1 (try -h)" ;;
    --poly-dir=*) poly_dir=${1##*=} ;;

    --symfpu-dir) die "missing argument to $1 (try -h)" ;;
    --symfpu-dir=*) symfpu_dir=${1##*=} ;;

    --lib-only) lib_only=ON ;;

    -*) die "invalid option '$1' (try -h)";;

    *) case $1 in
         production)      buildtype=Production;;
         debug)           buildtype=Debug;;
         testing)         buildtype=Testing;;
         competition)     buildtype=Competition;;
         competition-inc) buildtype=Competition; comp_inc=ON;;
         *)               die "invalid build type (try -h)";;
       esac
       ;;
  esac
  shift
done

#--------------------------------------------------------------------------#

cmake_opts=""

[ $buildtype != default ] \
  && cmake_opts="$cmake_opts -DCMAKE_BUILD_TYPE=$buildtype"

[ $asan != default ] \
  && cmake_opts="$cmake_opts -DENABLE_ASAN=$asan"
[ $ubsan != default ] \
  && cmake_opts="$cmake_opts -DENABLE_UBSAN=$ubsan"
[ $tsan != default ] \
  && cmake_opts="$cmake_opts -DENABLE_TSAN=$tsan"
[ $assertions != default ] \
  && cmake_opts="$cmake_opts -DENABLE_ASSERTIONS=$assertions"
[ $best != default ] \
  && cmake_opts="$cmake_opts -DENABLE_BEST=$best"
[ $comp_inc != default ] \
  && cmake_opts="$cmake_opts -DENABLE_COMP_INC_TRACK=$comp_inc"
[ $coverage != default ] \
  && cmake_opts="$cmake_opts -DENABLE_COVERAGE=$coverage"
[ $debug_symbols != default ] \
  && cmake_opts="$cmake_opts -DENABLE_DEBUG_SYMBOLS=$debug_symbols"
[ $debug_context_mm != default ] \
  && cmake_opts="$cmake_opts -DENABLE_DEBUG_CONTEXT_MM=$debug_context_mm"
[ $dumping != default ] \
  && cmake_opts="$cmake_opts -DENABLE_DUMPING=$dumping"
[ $gpl != default ] \
  && cmake_opts="$cmake_opts -DENABLE_GPL=$gpl"
[ $win64 != default ] \
  && cmake_opts="$cmake_opts -DCMAKE_TOOLCHAIN_FILE=../cmake/Toolchain-mingw64.cmake"
[ $ninja != default ] && cmake_opts="$cmake_opts -G Ninja"
[ $muzzle != default ] \
  && cmake_opts="$cmake_opts -DENABLE_MUZZLE=$muzzle"
[ $optimized != default ] \
  && cmake_opts="$cmake_opts -DENABLE_OPTIMIZED=$optimized"
[ $proofs != default ] \
  && cmake_opts="$cmake_opts -DENABLE_PROOFS=$proofs"
[ $shared != default ] \
  && cmake_opts="$cmake_opts -DENABLE_SHARED=$shared"
[ $static_binary != default ] \
  && cmake_opts="$cmake_opts -DENABLE_STATIC_BINARY=$static_binary"
[ $statistics != default ] \
  && cmake_opts="$cmake_opts -DENABLE_STATISTICS=$statistics"
[ $tracing != default ] \
  && cmake_opts="$cmake_opts -DENABLE_TRACING=$tracing"
[ $unit_testing != default ] \
  && cmake_opts="$cmake_opts -DENABLE_UNIT_TESTING=$unit_testing"
[ $python2 != default ] \
  && cmake_opts="$cmake_opts -DUSE_PYTHON2=$python2"
[ $python3 != default ] \
  && cmake_opts="$cmake_opts -DUSE_PYTHON3=$python3"
[ $python_bindings != default ] \
  && cmake_opts="$cmake_opts -DBUILD_BINDINGS_PYTHON=$python_bindings"
[ $java_bindings != default ] \
  && cmake_opts="$cmake_opts -DBUILD_BINDINGS_JAVA=$java_bindings"
[ $valgrind != default ] \
  && cmake_opts="$cmake_opts -DENABLE_VALGRIND=$valgrind"
[ $profiling != default ] \
  && cmake_opts="$cmake_opts -DENABLE_PROFILING=$profiling"
[ $editline != default ] \
  && cmake_opts="$cmake_opts -DUSE_EDITLINE=$editline"
[ $abc != default ] \
  && cmake_opts="$cmake_opts -DUSE_ABC=$abc"
[ $cadical != default ] \
  && cmake_opts="$cmake_opts -DUSE_CADICAL=$cadical"
[ $cln != default ] \
  && cmake_opts="$cmake_opts -DUSE_CLN=$cln"
[ $cryptominisat != default ] \
  && cmake_opts="$cmake_opts -DUSE_CRYPTOMINISAT=$cryptominisat"
[ $drat2er != default ] \
  && cmake_opts="$cmake_opts -DUSE_DRAT2ER=$drat2er"
[ $glpk != default ] \
  && cmake_opts="$cmake_opts -DUSE_GLPK=$glpk"
[ $kissat != default ] \
  && cmake_opts="$cmake_opts -DUSE_KISSAT=$kissat"
[ $lfsc != default ] \
  && cmake_opts="$cmake_opts -DUSE_LFSC=$lfsc"
[ $poly != default ] \
  && cmake_opts="$cmake_opts -DUSE_POLY=$poly"
[ $symfpu != default ] \
  && cmake_opts="$cmake_opts -DUSE_SYMFPU=$symfpu"
[ "$abc_dir" != default ] \
  && cmake_opts="$cmake_opts -DABC_DIR=$abc_dir"
[ "$antlr_dir" != default ] \
  && cmake_opts="$cmake_opts -DANTLR_DIR=$antlr_dir"
[ "$cadical_dir" != default ] \
  && cmake_opts="$cmake_opts -DCADICAL_DIR=$cadical_dir"
[ "$cryptominisat_dir" != default ] \
  && cmake_opts="$cmake_opts -DCRYPTOMINISAT_DIR=$cryptominisat_dir"
[ "$cxxtest_dir" != default ] \
  && cmake_opts="$cmake_opts -DCXXTEST_DIR=$cxxtest_dir"
[ "$drat2er_dir" != default ] \
  && cmake_opts="$cmake_opts -DDRAT2ER_DIR=$drat2er_dir"
[ "$glpk_dir" != default ] \
  && cmake_opts="$cmake_opts -DGLPK_DIR=$glpk_dir"
[ "$gmp_dir" != default ] \
  && cmake_opts="$cmake_opts -DGMP_DIR=$gmp_dir"
[ "$kissat_dir" != default ] \
  && cmake_opts="$cmake_opts -DKISSAT=$kissat_dir"
[ "$lfsc_dir" != default ] \
  && cmake_opts="$cmake_opts -DLFSC_DIR=$lfsc_dir"
[ "$poly_dir" != default ] \
  && cmake_opts="$cmake_opts -DPOLY_DIR=$poly_dir"
[ "$symfpu_dir" != default ] \
  && cmake_opts="$cmake_opts -DSYMFPU_DIR=$symfpu_dir"
[ "$lib_only" != default ] \
    && cmake_opts="$cmake_opts -DBUILD_LIB_ONLY=$lib_only"
[ "$install_prefix" != default ] \
  && cmake_opts="$cmake_opts -DCMAKE_INSTALL_PREFIX=$install_prefix"
[ -n "$program_prefix" ] \
  && cmake_opts="$cmake_opts -DPROGRAM_PREFIX=$program_prefix"

root_dir=$(pwd)

# The cmake toolchain can't be changed once it is configured in $build_dir.
# Thus, remove $build_dir and create an empty directory.
[ $win64 = ON ] && [ -e "$build_dir" ] && rm -r "$build_dir"
mkdir -p "$build_dir"

cd "$build_dir"

[ -e CMakeCache.txt ] && rm CMakeCache.txt
build_dir_escaped=$(echo "$build_dir" | sed 's/\//\\\//g')
cmake "$root_dir" $cmake_opts 2>&1 | \
  sed "s/^Now just/Now change to '$build_dir_escaped' and/"
