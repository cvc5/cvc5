#!/usr/bin/env bash
###############################################################################
# Top contributors (to current version):
#   Makai Mann, Alex Ozdemir, Gereon Kremer
#
# This file is part of the cvc5 project.
#
# Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
# in the top-level source directory and their institutional affiliations.
# All rights reserved.  See the file COPYING in the top-level source
# directory for licensing information.
# ############################################################################
#
# Build the python wheel for cvc5 with a given python interpreter and additional
# configuration arguments in a clean build folder.
# Call as follows:
#   contrib/packaging_python/mk_clean_wheel.sh /usr/bin/python3 "--cadical"
#
# The script first sets up a python venv with the given interpreter and installs
# some requirements in this venv. It then uses the mk_build_dir.py script to
# prepare a fresh build folder build_wheel/ and builds the wheel in there using
# mk_wheel.py. The wheel is fixes (using auditwheel or delocate-wheel) and
# copied out of the build folder.
##

PYTHONBIN=$1
CONFIG="$2"
PYVERSION=$($PYTHONBIN -c "import sys; print(sys.implementation.name + sys.version.split()[0])")

# setup and activate venv
echo "Making venv with $PYTHONBIN"
ENVDIR=env$PYVERSION
$PYTHONBIN -m venv ./$ENVDIR
source ./$ENVDIR/bin/activate

# install packages
pip install -q --upgrade pip setuptools auditwheel
pip install -q Cython pytest toml scikit-build flex pyparsing 
if [ "$(uname)" == "Darwin" ]; then
    # Mac version of auditwheel
    pip install -q delocate
fi

# configure cvc5
echo "Configuring"
rm -rf build_wheel/
python contrib/packaging_python/mk_build_dir.py $CONFIG --python-bindings --name=build_wheel

# building wheel
echo "Building pycvc5 wheel"

pushd build_wheel
python ../contrib/packaging_python/mk_wheel.py bdist_wheel -d dist

cd dist

# resolve the links and bundle the library with auditwheel
if [ "$(uname)" == "Linux" ]; then
    auditwheel show ./*.whl
    auditwheel repair ./*.whl
elif [ "$(uname)" == "Darwin" ]; then
    delocate-wheel -w wheelhouse ./*.whl
else
    echo "Unhandled system $(uname) for packing libraries with wheel."
fi

popd

mv build_wheel/dist/wheelhouse/*.whl .
