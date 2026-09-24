#!/usr/bin/env bash
###############################################################################
# This file is part of the cvc5 project.
#
# Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
# in the top-level source directory and their institutional affiliations.
# All rights reserved.  See the file COPYING in the top-level source
# directory for licensing information.
# #############################################################################
#
# Set up Murxla (https://github.com/murxla/murxla) and fuzz the current code.
#
# Everything lives in build-murxla/: a shared build of cvc5 installed into
# build-murxla/install and a Murxla checkout built against it. cvc5 and Murxla
# are rebuilt and cvc5 is reinstalled on every run so that Murxla always fuzzes
# the current code.
#
# Usage: contrib/run-murxla.sh [<options>] [<murxla options>]
#        contrib/run-murxla.sh --coverage-report
#
# Options:
#   --configure "<args>"  pass <args> on to configure.sh
#                         [default: "testing --cocoa --gpl"]
#   --static              build cvc5 and Murxla statically
#   --coverage            instrument cvc5 and write a coverage report
#   --coverage-keep       like --coverage, but keep the data of previous runs
#   --coverage-report     only regenerate the coverage report
#
# Without Murxla options Murxla runs in continuous mode with a 5s time limit
# per test run and delta debugs the traces it finds. Error traces are written
# to the current working directory.
#
# The configure.sh arguments select the build type and the optional features
# of cvc5, e.g. --configure "safe --cocoa --gpl". The default is an optimized
# build with assertions that includes CoCoA, which Murxla needs to fuzz finite
# fields. If they differ from the arguments that the build tree was configured
# with, cvc5 is reconfigured in place and Murxla is rebuilt. Use BUILD_DIR to
# keep builds with different arguments side by side.
#
# Static mode builds cvc5 as a static library and links the Murxla binary
# against it without any shared libraries, so that it can be copied to a
# machine that has none of the dependencies installed.
#
# Coverage mode instruments cvc5 and writes a report when Murxla exits. Like
# any cvc5 coverage build it requires fastcov, lcov and genhtml.
#
# Both modes use their own build tree (build-murxla-static/, build-murxla-cov/)
# so that switching between modes does not rebuild everything. Coverage
# counters are reset on startup, --coverage-keep instead accumulates onto the
# data of previous sessions and --coverage-report only regenerates the report
# from the data on disk.
##

set -e -o pipefail

MURXLA_REPO="https://github.com/murxla/murxla.git"

CONFIGURE_ARGS="testing --cocoa --gpl"
COVERAGE=0
REPORT_ONLY=0
KEEP_DATA=0
STATIC=0
while [ $# -gt 0 ]; do
  case "$1" in
    --configure)
      [ $# -ge 2 ] || { echo "*** missing argument to $1" >&2; exit 1; }
      CONFIGURE_ARGS="$2"; shift 2 ;;
    --configure=*)     CONFIGURE_ARGS="${1#*=}"; shift ;;
    --static)          STATIC=1; shift ;;
    --coverage)        COVERAGE=1; shift ;;
    --coverage-keep)   COVERAGE=1; KEEP_DATA=1; shift ;;
    --coverage-report) COVERAGE=1; REPORT_ONLY=1; shift ;;
    *) break ;;
  esac
done

CVC5_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
build_suffix=""
if [ "$STATIC" = 1 ]; then
  build_suffix="$build_suffix-static"
fi
if [ "$COVERAGE" = 1 ]; then
  build_suffix="$build_suffix-cov"
fi
BUILD_DIR="${BUILD_DIR:-$CVC5_DIR/build-murxla$build_suffix}"
INSTALL_DIR="$BUILD_DIR/install"
MURXLA_DIR="$BUILD_DIR/murxla"
MURXLA_BINARY="$MURXLA_DIR/build/bin/murxla"
COVERAGE_DIR="$BUILD_DIR/coverage"
COVERAGE_REPORT="$COVERAGE_DIR/index.html"
COVERAGE_INFO="$COVERAGE_DIR/coverage.info"
CONFIG_STAMP="$BUILD_DIR/run-murxla.config"

# Only report on cvc5's own sources, the counters of the dependencies built in
# $BUILD_DIR/deps say nothing about how well Murxla covers cvc5. The coverage
# target of the cvc5 build is not used since it searches the source directory
# for counter files, which misses a build tree outside of it.
generate_coverage_report()
{
  mkdir -p "$COVERAGE_DIR"
  fastcov -d "$BUILD_DIR/src" -i "$CVC5_DIR/src/" -b -X -j "$(nproc)" \
    --lcov -o "$COVERAGE_INFO"
  genhtml --branch-coverage --demangle-cpp --no-prefix -q \
    -o "$COVERAGE_DIR" "$COVERAGE_INFO"
  echo "-- coverage report: $COVERAGE_REPORT"
}

# A failed configure step leaves a CMakeCache.txt but no build system behind.
is_configured()
{
  [ -f "$1/build.ninja" ] || [ -f "$1/Makefile" ]
}

if [ "$REPORT_ONLY" = 1 ]; then
  generate_coverage_report
  exit 0
fi

# The defaults come first so that --configure can override them, the arguments
# that the setup below relies on come last. The library directory is pinned
# since static linking needs to know where the libraries of cvc5 and its
# dependencies are installed.
read -r -a user_configure_args <<< "$CONFIGURE_ARGS"
configure_args=(--auto-download --no-unit-testing -DCMAKE_INSTALL_MESSAGE=LAZY)
if command -v ninja > /dev/null; then
  configure_args+=(--ninja)
fi
configure_args+=("${user_configure_args[@]}")
configure_args+=(-DCMAKE_INSTALL_LIBDIR=lib
  --prefix="$INSTALL_DIR" --name="$BUILD_DIR")
murxla_cmake_args=()
murxla_cxx_flags=()
murxla_ld_flags=()
if [ "$STATIC" = 1 ]; then
  configure_args+=(--static)
  # The cvc5 package refers to the static libraries of its dependencies by
  # name only, they are installed next to the cvc5 library.
  murxla_ld_flags+=(-static -L"$INSTALL_DIR/lib")
else
  configure_args+=(--no-static)
fi
if [ "$COVERAGE" = 1 ]; then
  configure_args+=(--coverage)
  # MURXLA_COVERAGE makes Murxla dump the counters from its SIGABRT handler so
  # that aborted and timed out runs contribute coverage, too. Murxla has to be
  # linked with --coverage to get libgcov, which provides __gcov_dump(), the
  # instrumented cvc5 library does not export it. Murxla itself is not
  # instrumented.
  murxla_cxx_flags+=(-DMURXLA_COVERAGE)
  murxla_ld_flags+=(--coverage)
else
  configure_args+=(--no-coverage)
fi
if [ ${#murxla_cxx_flags[@]} -gt 0 ]; then
  murxla_cmake_args+=(-DCMAKE_CXX_FLAGS="${murxla_cxx_flags[*]}")
fi
if [ ${#murxla_ld_flags[@]} -gt 0 ]; then
  murxla_cmake_args+=(-DCMAKE_EXE_LINKER_FLAGS="${murxla_ld_flags[*]}")
fi

# The arguments are only recorded once configuring succeeded. configure.sh
# starts from a fresh CMake cache, the installed files and the Murxla build are
# removed as well so that nothing of a previous configuration is left behind.
if [ "$(cat "$CONFIG_STAMP" 2> /dev/null)" != "${configure_args[*]}" ]; then
  echo "-- configuring cvc5 in $BUILD_DIR"
  rm -rf "$INSTALL_DIR" "$MURXLA_DIR/build"
  (
    cd "$CVC5_DIR"
    ./configure.sh "${configure_args[@]}"
  )
  echo "${configure_args[*]}" > "$CONFIG_STAMP"
fi

echo "-- installing cvc5 into $INSTALL_DIR"
cmake --build "$BUILD_DIR" -j "$(nproc)"
cmake --install "$BUILD_DIR"

if [ ! -d "$MURXLA_DIR" ]; then
  echo "-- cloning Murxla into $MURXLA_DIR"
  git clone "$MURXLA_REPO" "$MURXLA_DIR"
fi

# Murxla picks up cvc5 via install/lib/cmake/cvc5/cvc5Config.cmake.
if ! is_configured "$MURXLA_DIR/build"; then
  echo "-- configuring Murxla in $MURXLA_DIR/build"
  cmake -S "$MURXLA_DIR" -B "$MURXLA_DIR/build" \
    -DCMAKE_BUILD_TYPE=Release \
    -DCMAKE_PREFIX_PATH="$INSTALL_DIR" \
    "${murxla_cmake_args[@]}" \
    -DENABLE_BITWUZLA=OFF \
    -DENABLE_BOOLECTOR=OFF \
    -DENABLE_YICES=OFF
fi

# The installed cvc5 library is a link dependency of Murxla, this only relinks
# Murxla if cvc5 changed (and recompiles it if the cvc5 headers changed).
echo "-- building Murxla in $MURXLA_DIR/build"
cmake --build "$MURXLA_DIR/build" -j "$(nproc)"

args=("$@")
if [ ${#args[@]} -eq 0 ]; then
  args=(-t 5 -d)
fi
# Traces already encode the solver, --cvc5 must not be given on replay.
case " ${args[*]} " in
  *" -u "* | *" --untrace "*) ;;
  *) args=(--cvc5 "${args[@]}") ;;
esac

# Counter files accumulate over runs and go stale on recompilation.
if [ "$COVERAGE" = 1 ] && [ "$KEEP_DATA" = 0 ]; then
  echo "-- resetting coverage counters"
  find "$BUILD_DIR" -name '*.gcda' -delete
fi

echo "-- $MURXLA_BINARY ${args[*]}"
if [ "$COVERAGE" = 0 ]; then
  exec "$MURXLA_BINARY" "${args[@]}"
fi

# Ctrl+C terminates Murxla gracefully, keep the wrapper alive so that it still
# generates the report. This installs a handler instead of ignoring the signal,
# an ignored disposition would be inherited by Murxla.
trap 'echo' INT
"$MURXLA_BINARY" "${args[@]}" || true
generate_coverage_report
