#!/bin/sh
# Install dependencies in a centos environment (e.g. for manylinux for Python wheels)

# NOTE manylinux doesn't seem to have cln-devel -- leaving out, it's optional

yum update
yum install -y \
    gcc \
    gcc-c++ \
    make \
    ccache \
    cxxtest \
    gmp-devel \
    libedit-devel \
    gtest-devel \
    flex-devel \
    java-1.8.0-openjdk


DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" >/dev/null 2>&1 && pwd )"
CVC4_DIR=$DIR/../../

$CVC4_DIR/contrib/get-antlr-3.4
