#!/usr/bin/env bash

source "$(dirname "$0")/get-script-header.sh"

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
HOST="$HOST" contrib/get-gmp-dev || reporterror
