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
PLATFORM="$3"
PYVERSION=$($PYTHONBIN -c "import sys; print(sys.implementation.name + sys.version.split()[0])")

# This is needed because of scikit, otherwise it will include files from another
# python version installed in the system. 
PYINCLUDE=$($PYTHONBIN -c "import sysconfig; print(sysconfig.get_paths()['include'])")

# setup and activate venv
echo "Making venv with $PYTHONBIN"
ENVDIR=env$PYVERSION
$PYTHONBIN -m venv ./$ENVDIR
source ./$ENVDIR/bin/activate

# install packages
pip install -q --upgrade pip setuptools auditwheel
pip install -r contrib/requirements_build.txt
pip install -r contrib/requirements_python_dev.txt
if [ "$(uname)" == "Darwin" ]; then
    # Mac version of auditwheel
    pip install -q delocate
fi

# configure cvc5
echo "Configuring"
rm -rf build_wheel/

# This new command like is supposed to ensure that we use the python 
# version from the virtual environment that is activated. 
# Once we remove scikit, this will not be necessary.
./configure.sh $CONFIG --python-bindings --name=build_wheel -DPython_FIND_VIRTUALENV=ONLY -DPYTHON_LIBRARY=$VIRTUAL_ENV/lib -DPYTHON_INCLUDE_DIR=$PYINCLUDE

# building wheel
echo "Building pycvc5 wheel"

pushd build_wheel
# Copy the license files to be included in the wheel
cmake --build . --target cvc5_python_licenses
if [ -z "$PLATFORM" ] ; then
  python ../contrib/packaging_python/mk_wheel.py bdist_wheel -d dist
else
  python ../contrib/packaging_python/mk_wheel.py bdist_wheel -d dist --plat-name $PLATFORM
fi

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
