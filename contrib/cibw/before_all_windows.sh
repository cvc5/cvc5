#!/usr/bin/env bash

python3 -m pip install --user -r contrib/requirements_build.txt

./configure.sh production --auto-download --python-bindings --python-only-src --win64-native --prefix=./install

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
