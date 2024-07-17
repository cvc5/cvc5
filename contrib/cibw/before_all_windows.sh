#!/usr/bin/env bash

GPL="$1"

COMMON_CMD="./configure.sh production --auto-download --python-bindings --python-only-src --prefix=./install"

if [ "$GPL" = "true" ]; then
  GPL_FLAGS="--gpl --cln --glpk --cocoa"
else
  GPL_FLAGS=""
fi

$COMMON_CMD $GPL_FLAGS

SETUP_CFG=./build/src/api/python/setup.cfg
echo "[build_ext]" > ${SETUP_CFG}
echo "include_dirs=$(cygpath -m $(pwd)/install/include)" >> ${SETUP_CFG}
echo "library_dirs=$(cygpath -m $(pwd)/install/lib)" >> ${SETUP_CFG}
echo "[build]" >> ${SETUP_CFG}
echo "compiler = mingw32" >> ${SETUP_CFG}
cat ${SETUP_CFG}

pushd build
make -j$(( $(nproc) + 1 ))
make install
popd
