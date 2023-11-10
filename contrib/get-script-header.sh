#!/usr/bin/env bash
#
set -e -o pipefail

[ ! -d contrib ] && echo "$0 not called from base directory" && exit 1

DEPS_DIR="$(pwd)/deps"
INSTALL_DIR="$DEPS_DIR/install"
INSTALL_LIB_DIR="$INSTALL_DIR/lib"
INSTALL_INCLUDE_DIR="$INSTALL_DIR/include"
INSTALL_BIN_DIR="$INSTALL_DIR/bin"

mkdir -p "$DEPS_DIR"


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

function setup_dep
{
  url="$1"
  directory="$2"
  echo "Setting up $directory ..."
  rm -rf "$directory"
  mkdir -p "$directory"
  cd "$directory"
  webget "$url" archive
  tar xf archive --strip 1 # Strip top-most directory
  rm archive
}

# Some of our dependencies do not provide a make install rule. Use the
# following helper functions to copy libraries/headers/binaries into the
# corresponding directories in deps/install.

function install_lib
{
  echo "Copying $1 to $INSTALL_LIB_DIR"
  [ ! -d "$INSTALL_LIB_DIR" ] && mkdir -p "$INSTALL_LIB_DIR"
  cp "$1" "$INSTALL_LIB_DIR"
}

function install_includes
{
  include="$1"
  subdir="$2"
  echo "Copying $1 to $INSTALL_INCLUDE_DIR/$subdir"
  [ ! -d "$INSTALL_INCLUDE_DIR" ] && mkdir -p "$INSTALL_INCLUDE_DIR"
  [ -n "$subdir" ] && [ ! -d "$INSTALL_INCLUDE_DIR/$subdir" ] && mkdir -p "$INSTALL_INCLUDE_DIR/$subdir"
  cp -r "$include" "$INSTALL_INCLUDE_DIR/$subdir"
}

function install_bin
{
  echo "Copying $1 to $INSTALL_BIN_DIR"
  [ ! -d "$INSTALL_BIN_DIR" ] && mkdir -p "$INSTALL_BIN_DIR"
  cp "$1" "$INSTALL_BIN_DIR"
}

function guess_lib_dir
{
   #
   # On some systems the library may be installed to lib64/
   # instead of lib/
   #
   # This function guesses the install lib directory
   #
   lib_name="$1"
   lib_dir="$(dirname "$(find "$INSTALL_DIR" -name "${lib_name}")")"
   echo ${lib_dir}
}

function rename_installed_lib
{
   #
   # This function uses the calculated library directory and
   # then relocates the first argument to the second.
   #
   src="$1"
   dest="$2"
   lib_dir="$(guess_lib_dir "$src")"
   mv "$lib_dir/$src" "$lib_dir/$dest"
}

