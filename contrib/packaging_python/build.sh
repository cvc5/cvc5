#!/usr/bin/env bash

set -xe

OPTS="production --auto-download"

pwd

echo $PATH

for version in $1
do
    VERSION_SUFFIX="$2" ./contrib/packaging_python/create_wheel.sh /opt/python/cp${version}-cp${version}m/bin/python "$OPTS"
done

cp dist*/*.whl .
