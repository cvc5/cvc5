#!/bin/bash
#
set -e

cd "$(dirname "$0")/.."

if ! [ -e src/parser/cvc/Cvc.g ]; then
  echo "$(basename $0): I expect to be in the contrib/ of a CVC4 source tree," >&2
  echo "but apparently:" >&2
  echo >&2
  echo "  $(pwd)" >&2
  echo >&2
  echo "is not a CVC4 source tree ?!" >&2
  exit 1
fi

function webget {
  if which wget &>/dev/null; then
    wget -c -O "$2" "$1"
  elif which curl &>/dev/null; then
    curl "$1" >"$2"
  else
    echo "Can't figure out how to download from web.  Please install wget or curl." >&2
    exit 1
  fi
}
