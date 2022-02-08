#!/bin/bash

PYTHONBIN=$1
CONFIG="$2"
VERSION=$($PYTHONBIN -c "import sys; print(sys.version.split()[0])")

# setup and activate venv
echo "Making venv with $PYTHONBIN"
ENVDIR=env$VERSION
$PYTHONBIN -m venv ./$ENVDIR
source ./$ENVDIR/bin/activate

# install packages
pip install -q --upgrade pip setuptools auditwheel
pip install -q twine Cython pytest toml scikit-build
if [ "$(uname)" == "Darwin" ]; then
    # Mac version of auditwheel
    pip install -q delocate
fi

# configure cvc5
echo "Configuring"
python contrib/packaging_python/mk_build_dir.py $CONFIG --python-bindings

# building wheel
echo "Building pycvc5 wheel"

pushd build_wheel
DISTDIR=dist
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

rm -rf wheel-$VERSION
mv build_wheel/dist wheel-$VERSION
