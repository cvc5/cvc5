#!/usr/bin/env bash

GPL="$1"

COMMON_CMD="./configure.sh production --auto-download --python-bindings --python-only-src --prefix=./install -DBUILD_GMP=1"

if [ "$GPL" = "true" ]; then
  # Install build dependencies for GPL libraries
  brew install autoconf automake libtool
  GPL_FLAGS="--gpl --cln --glpk --cocoa"
else
  GPL_FLAGS=""
fi

$COMMON_CMD $GPL_FLAGS

SETUP_CFG=./build/src/api/python/setup.cfg
echo "[build_ext]" > ${SETUP_CFG}
echo "include_dirs=$(pwd)/install/include" >> ${SETUP_CFG}
echo "library_dirs=$(pwd)/install/lib" >> ${SETUP_CFG}
cat ${SETUP_CFG}

pushd build
make -j$(( $(sysctl -n hw.logicalcpu) + 1 ))
make install
popd
