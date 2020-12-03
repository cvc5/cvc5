#!/bin/sh
# Install dependencies GitHub actions in a centos environment (e.g. for manylinux for Python wheels)

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
    flex-devel

