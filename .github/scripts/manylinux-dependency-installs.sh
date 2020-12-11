#!/bin/sh
# Install dependencies in a centos environment (e.g. for manylinux for Python wheels)
# https://github.com/pypa/manylinux
# used in .github/workflows/wheels.yml

yum update
yum install -y \
    gcc \
    gcc-c++ \
    make \
    gmp-devel \
    libedit-devel \
    flex-devel \
    java-1.8.0-openjdk


DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" >/dev/null 2>&1 && pwd )"
CVC4_DIR=$DIR/../../

$CVC4_DIR/contrib/get-antlr-3.4
