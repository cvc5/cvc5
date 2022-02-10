#!/bin/bash

PYTHONBIN=$1
CONFIG="$2"
PYVERSION=$($PYTHONBIN -c "import sys; print(sys.implementation.name + sys.version.split()[0])")

# setup and activate venv
echo "Making venv with $PYTHONBIN"
ENVDIR=env$PYVERSION
$PYTHONBIN -m venv ./$ENVDIR
source ./$ENVDIR/bin/activate

which python

# install packages
pip install -q --upgrade pip setuptools auditwheel
pip install -q Cython pytest toml scikit-build
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
