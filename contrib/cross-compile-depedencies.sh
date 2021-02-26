#!/usr/bin/env bash

source "$(dirname "$0")/get-script-header.sh"

export MAKE_CFLAGS=
export MAKE_CXXFLAGS=
export MAKE_LDFLAGS=
export BUILD_TYPE="--disable-shared --enable-static"
while getopts ":s" opt; do
  case ${opt} in
    s )
      MAKE_CFLAGS="-static-libgcc -static-libstdc++"
      MAKE_CXXFLAGS="-static-libgcc -static-libstdc++"
      # CVC4 uses some internal symbols of ANTLR, so all symbols need to be
      # exported
      MAKE_LDFLAGS="-no-undefined -Wl,--export-all-symbols"
      BUILD_TYPE="--enable-shared --disable-static"
      ;;
  esac
done

function reporterror {
  echo
  echo =============================================================================
  echo
  echo "There was an error setting up the prerequisites.  Look above for details."
  echo
  exit 1
}

if [ -z "$HOST" ]; then
  echo "No HOST specified, use e.g.,"
  echo "  HOST=aarch64-linux-gnu for ARM 64 bit Linux builds"
  echo "  HOST=x86_64-w64-mingw32 for Windows 64 bit builds"
  exit 1
fi

MACHINE_TYPE="$(echo "$HOST" | cut -d '-' -f 1)"
echo "Using MACHINE_TYPE=$MACHINE_TYPE for HOST=$HOST"
export MACHINE_TYPE

ANTLR_CONFIGURE_ARGS="--host=$HOST" contrib/get-antlr-3.4 || reporterror

# Setup GMP
HOST="$HOST" \
BUILD_TYPE="$BUILD_TYPE" \
MAKE_CFLAGS="$MAKE_CFLAGS" \
MAKE_CXXFLAGS="$MAKE_CXXFLAGS" \
MAKE_LDFLAGS="$MAKE_LDFLAGS" \
  contrib/get-gmp-dev || reporterror
