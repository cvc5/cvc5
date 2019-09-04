#!/usr/bin/env bash
#
set -e -o pipefail

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
  if [ -x "$(command -v wget)" ]; then
    wget -c -O "$2" "$1"
  elif [ -x "$(command -v curl)" ]; then
    curl -L "$1" >"$2"
  else
    echo "Can't figure out how to download from web.  Please install wget or curl." >&2
    exit 1
  fi
}

for cmd in python python2 python3; do
  if [ -x "$(command -v $cmd)" ]; then
    PYTHON="$cmd"
    break
  fi
done

if [ -z "$PYTHON" ]; then
  echo "Error: Couldn't find python, python2, or python3." >&2
  exit 1
fi
