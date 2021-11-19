#!/usr/bin/env bash

set -xe

git clone https://github.com/cvc5/cvc5.git

cd cvc5

echo VERSION_SUFFIX: "$1"

VERSION_SUFFIX="$1" ../shared/create_wheel.sh /opt/python/cp36-cp36m/bin/python
VERSION_SUFFIX="$1" ../shared/create_wheel.sh /opt/python/cp37-cp37m/bin/python
VERSION_SUFFIX="$1" ../shared/create_wheel.sh /opt/python/cp38-cp38/bin/python
VERSION_SUFFIX="$1" ../shared/create_wheel.sh /opt/python/cp39-cp39/bin/python
VERSION_SUFFIX="$1" ../shared/create_wheel.sh /opt/python/cp310-cp310/bin/python

cp dist*/wheelhouse/*.whl ../build
