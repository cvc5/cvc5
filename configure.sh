#!/usr/bin/env bash
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
  --best                   turn on dependencies and options known to give best performance
  --gpl                    permit GPL dependencies, if available
  --arm64                  cross-compile for Linux ARM 64 bit
  --win64                  cross-compile for Windows 64 bit
  --win64-native           natively compile for Windows 64 bit
  --ninja                  use Ninja build system
  --docs                   build Api documentation


Features:
The following flags enable optional features (disable with --no-<option name>).
  --static                 build static libraries and binaries [default=no]
  --static-binary          link against static system libraries
  --auto-download          automatically download dependencies if necessary
  --debug-symbols          include debug symbols
  --valgrind               Valgrind instrumentation
  --debug-context-mm       use the debug context memory manager
  --statistics             include statistics
  --assertions             turn on assertions
  --tracing                include tracing code
  --muzzle                 complete silence (no non-result output)
  --coverage               support for gcov coverage testing
  --profiling              support for gprof profiling
  --unit-testing           support for unit testing
  --python-bindings        build Python bindings based on new C++ API
  --java-bindings          build Java bindings based on new C++ API
  --all-bindings           build bindings for all supported languages
  --asan                   build with ASan instrumentation
  --ubsan                  build with UBSan instrumentation
  --tsan                   build with TSan instrumentation
  --werror                 build with -Werror
  --ipo                    build with interprocedural optimization

Optional Packages:
The following flags enable optional packages (disable with --no-<option name>).
  --cln                    use CLN instead of GMP
  --glpk                   use GLPK simplex solver
  --cryptominisat          use the CryptoMiniSat SAT solver
  --kissat                 use the Kissat SAT solver
  --poly                   use the LibPoly library [default=yes]
  --cocoa                  use the CoCoA library
  --editline               support the editline library

Optional Path to Optional Packages:
  --glpk-dir=PATH          path to top level of GLPK installation
  --dep-path=PATH          path to a dependency installation dir

CMake Options (Advanced)
  -DVAR=VALUE              manually add CMake options

Wasm Options
  --wasm=VALUE             set compilation extension for WebAssembly <WASM, JS or HTML>
  --wasm-flags='STR'       Emscripten flags used in the WebAssembly binary compilation

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

asan=default
assertions=default
auto_download=default
cln=default
comp_inc=default
coverage=default
cryptominisat=default
debug_context_mm=default
debug_symbols=default
docs=default
glpk=default
gpl=default
kissat=default
poly=ON
cocoa=default
muzzle=default
ninja=default
profiling=default
python_bindings=default
java_bindings=default
editline=default
build_shared=ON
static_binary=default
statistics=default
tracing=default
tsan=default
ubsan=default
unit_testing=default
valgrind=default
win64=default
win64_native=default
arm64=default
werror=default
ipo=default

glpk_dir=default

wasm=default
wasm_flags=""

#--------------------------------------------------------------------------#

cmake_opts=""

while [ $# -gt 0 ]
do
  case $1 in

    -h|--help) usage;;

    --asan) asan=ON;;
    --no-asan) asan=OFF;;

    --ubsan) ubsan=ON;;
    --no-ubsan) ubsan=OFF;;

    --tsan) tsan=ON;;
    --no-tsan) tsan=OFF;;

    --werror) werror=ON;;

    --ipo) ipo=ON;;
    --no-ipo) ipo=OFF;;

    --assertions) assertions=ON;;
    --no-assertions) assertions=OFF;;

    # Best configuration
    --best)
      cln=ON
      cryptominisat=ON
      editline=ON
      glpk=ON
      ipo=ON
      ;;

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

    --gpl) gpl=ON;;
    --no-gpl) gpl=OFF;;

    --kissat) kissat=ON;;
    --no-kissat) kissat=OFF;;

    --win64) win64=ON;;

    --win64-native) win64_native=ON;;

    --arm64) arm64=ON;;

    --ninja) ninja=ON;;

    --docs) docs=ON;;
    --no-docs) docs=OFF;;

    --glpk) glpk=ON;;
    --no-glpk) glpk=OFF;;

    --poly) poly=ON;;
    --no-poly) poly=OFF;;

    --cocoa) cocoa=ON;;
    --no-cocoa) cocoa=OFF;;

    --muzzle) muzzle=ON;;
    --no-muzzle) muzzle=OFF;;

    --static) build_shared=OFF;;
    --no-static) build_shared=ON;;

    --static-binary) static_binary=ON;;
    --no-static-binary) static_binary=OFF;;

    --auto-download) auto_download=ON;;
    --no-auto-download) auto_download=OFF;;

    --statistics) statistics=ON;;
    --no-statistics) statistics=OFF;;

    --tracing) tracing=ON;;
    --no-tracing) tracing=OFF;;

    --unit-testing) unit_testing=ON;;
    --no-unit-testing) unit_testing=OFF;;

    --python-bindings) python_bindings=ON;;
    --no-python-bindings) python_bindings=OFF;;

    --java-bindings) java_bindings=ON;;
    --no-java-bindings) java_bindings=OFF;;

    --all-bindings)
      python_bindings=ON
      java_bindings=ON;;

    --valgrind) valgrind=ON;;
    --no-valgrind) valgrind=OFF;;

    --profiling) profiling=ON;;
    --no-profiling) profiling=OFF;;

    --editline) editline=ON;;
    --no-editline) editline=OFF;;

    --glpk-dir) die "missing argument to $1 (try -h)" ;;
    --glpk-dir=*) glpk_dir=${1##*=} ;;

    --dep-path) die "missing argument to $1 (try -h)" ;;
    --dep-path=*) dep_path="${dep_path};${1##*=}" ;;

    --wasm) wasm=WASM ;;
    --wasm=*) wasm="${1##*=}" ;;

    --wasm-flags) die "missing argument to $1 (try -h)" ;;
    --wasm-flags=*) wasm_flags="${1#*=}" ;;

    -D*) cmake_opts="${cmake_opts} $1" ;;

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

if [ $werror != default ]; then
  export CFLAGS=-Werror
  export CXXFLAGS=-Werror
fi

[ $buildtype != default ] \
  && cmake_opts="$cmake_opts -DCMAKE_BUILD_TYPE=$buildtype"

[ $asan != default ] \
  && cmake_opts="$cmake_opts -DENABLE_ASAN=$asan"
[ $auto_download != default ] \
  && cmake_opts="$cmake_opts -DENABLE_AUTO_DOWNLOAD=$auto_download"
[ $ubsan != default ] \
  && cmake_opts="$cmake_opts -DENABLE_UBSAN=$ubsan"
[ $tsan != default ] \
  && cmake_opts="$cmake_opts -DENABLE_TSAN=$tsan"
[ $ipo != default ] \
  && cmake_opts="$cmake_opts -DENABLE_IPO=$ipo"
[ $assertions != default ] \
  && cmake_opts="$cmake_opts -DENABLE_ASSERTIONS=$assertions"
[ $comp_inc != default ] \
  && cmake_opts="$cmake_opts -DENABLE_COMP_INC_TRACK=$comp_inc"
[ $coverage != default ] \
  && cmake_opts="$cmake_opts -DENABLE_COVERAGE=$coverage"
[ $debug_symbols != default ] \
  && cmake_opts="$cmake_opts -DENABLE_DEBUG_SYMBOLS=$debug_symbols"
[ $debug_context_mm != default ] \
  && cmake_opts="$cmake_opts -DENABLE_DEBUG_CONTEXT_MM=$debug_context_mm"
[ $gpl != default ] \
  && cmake_opts="$cmake_opts -DENABLE_GPL=$gpl"
[ $win64 != default ] \
  && cmake_opts="$cmake_opts -DCMAKE_TOOLCHAIN_FILE=../cmake/Toolchain-mingw64.cmake"
# Because 'MSYS Makefiles' has a space in it, we set the variable vs. adding to 'cmake_opts'
[ $win64_native != default ] \
  && [ $ninja == default ] && export CMAKE_GENERATOR="MSYS Makefiles"
[ $arm64 != default ] \
  && cmake_opts="$cmake_opts -DCMAKE_TOOLCHAIN_FILE=../cmake/Toolchain-aarch64.cmake"
[ $ninja != default ] && cmake_opts="$cmake_opts -G Ninja"
[ $muzzle != default ] \
  && cmake_opts="$cmake_opts -DENABLE_MUZZLE=$muzzle"
[ $build_shared != default ] \
  && cmake_opts="$cmake_opts -DBUILD_SHARED_LIBS=$build_shared"
[ $static_binary != default ] \
  && cmake_opts="$cmake_opts -DSTATIC_BINARY=$static_binary"
[ $statistics != default ] \
  && cmake_opts="$cmake_opts -DENABLE_STATISTICS=$statistics"
[ $tracing != default ] \
  && cmake_opts="$cmake_opts -DENABLE_TRACING=$tracing"
[ $unit_testing != default ] \
  && cmake_opts="$cmake_opts -DENABLE_UNIT_TESTING=$unit_testing"
[ $docs != default ] \
  && cmake_opts="$cmake_opts -DBUILD_DOCS=$docs"
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
[ $cln != default ] \
  && cmake_opts="$cmake_opts -DUSE_CLN=$cln"
[ $cryptominisat != default ] \
  && cmake_opts="$cmake_opts -DUSE_CRYPTOMINISAT=$cryptominisat"
[ $glpk != default ] \
  && cmake_opts="$cmake_opts -DUSE_GLPK=$glpk"
[ $kissat != default ] \
  && cmake_opts="$cmake_opts -DUSE_KISSAT=$kissat"
[ $poly != default ] \
  && cmake_opts="$cmake_opts -DUSE_POLY=$poly"
[ $cocoa != default ] \
  && cmake_opts="$cmake_opts -DUSE_COCOA=$cocoa"
[ "$glpk_dir" != default ] \
  && cmake_opts="$cmake_opts -DGLPK_DIR=$glpk_dir"
[ "$dep_path" != default ] \
  && cmake_opts="$cmake_opts -DCMAKE_PREFIX_PATH=$dep_path"
[ "$install_prefix" != default ] \
  && cmake_opts="$cmake_opts -DCMAKE_INSTALL_PREFIX=$install_prefix"
[ -n "$program_prefix" ] \
  && cmake_opts="$cmake_opts -DPROGRAM_PREFIX=$program_prefix"
[ "$wasm" != default ] \
  && cmake_opts="$cmake_opts -DWASM=$wasm"

root_dir=$(pwd)

cmake_wrapper=
cmake_opts=($cmake_opts)
if [ "$wasm" == "WASM" ] || [ "$wasm" == "JS" ] || [ "$wasm" == "HTML" ] ; then
  cmake_wrapper=emcmake
  cmake_opts=(${cmake_opts[@]} -DWASM_FLAGS="${wasm_flags}")
fi

# The cmake toolchain can't be changed once it is configured in $build_dir.
# Thus, remove $build_dir and create an empty directory.
[ $win64 = ON ] && [ -e "$build_dir" ] && rm -r "$build_dir"
[ $arm64 = ON ] && [ -e "$build_dir" ] && rm -r "$build_dir"
mkdir -p "$build_dir"

cd "$build_dir"

[ -e CMakeCache.txt ] && rm CMakeCache.txt
build_dir_escaped=$(echo "$build_dir" | sed 's/\//\\\//g')
$cmake_wrapper cmake "$root_dir" "${cmake_opts[@]}" 2>&1 | \
  sed "s/^Now just/Now change to '$build_dir_escaped' and/"
