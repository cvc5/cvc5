#####################
## setup.py
## Top contributors (to current version):
##   Makai Mann
## This file is part of the CVC4 project.
## Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
## in the top-level source directory and their institutional affiliations.
## All rights reserved.  See the file COPYING in the top-level source
## directory for licensing information.
##
## This setup.py will build CVC4 using the CMake arguments in cmake_args below
## This is primarily intended for building Python wheels to be uploaded to PyPi.
## If you are installing from source, this is not the recommended way to build
## CVC4 (it does not allow you to customize the options and it will hide the
## build folder). Please instead use the main approach:
##
## ./configure.sh [your options] --python-bindings
## (since you're looking at this setup.py, you probably want python bindings)
## cd build
## make
##

from skbuild import setup

setup(
    name="pycvc4",
    version="1.9.0",
    license="BSD",
    packages=['pycvc4'],
    package_dir={
        'pycvc4': 'src/api/pycvc4'},
    cmake_args=['-DBUILD_BINDINGS_PYTHON=ON', '-DENABLE_SHARED=OFF', '-DBUILD_LIB_ONLY=ON']
)
