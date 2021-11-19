#!/usr/bin/env bash

set -xe

echo VERSION_SUFFIX: "$1"

OPTS="production --auto-download"

VERSION_SUFFIX="$1" ./contrib/packaging_python/create_wheel.sh /opt/python/cp36-cp36m/bin/python "$OPTS"
VERSION_SUFFIX="$1" ./contrib/packaging_python/create_wheel.sh /opt/python/cp37-cp37m/bin/python "$OPTS"
VERSION_SUFFIX="$1" ./contrib/packaging_python/create_wheel.sh /opt/python/cp38-cp38/bin/python "$OPTS"
VERSION_SUFFIX="$1" ./contrib/packaging_python/create_wheel.sh /opt/python/cp39-cp39/bin/python "$OPTS"
VERSION_SUFFIX="$1" ./contrib/packaging_python/create_wheel.sh /opt/python/cp310-cp310/bin/python "$OPTS"

#cp dist*/wheelhouse/*.whl ../build
ls -al
ls -al dist*/