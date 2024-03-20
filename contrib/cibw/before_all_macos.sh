#!/usr/bin/env bash

python3 -m pip install --user -r contrib/requirements_build.txt

./configure.sh production --auto-download \
  --python-bindings --python-only-src --prefix=./install -DBUILD_GMP=1

SETUP_CFG=./build/src/api/python/setup.cfg
echo "[build_ext]" > ${SETUP_CFG}
echo "include_dirs=$(pwd)/install/include" >> ${SETUP_CFG}
echo "library_dirs=$(pwd)/install/lib" >> ${SETUP_CFG}
cat ${SETUP_CFG}

pushd build
make -j$(( $(sysctl -n hw.logicalcpu) + 1 ))
make install
popd
