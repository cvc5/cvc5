#!/bin/bash

DIR=$(pwd)

PYTHONBIN=$1
CONFIG="$2"
VERSION=$($PYTHONBIN -c "import sys; print(sys.version.split()[0])")

# setup and activate venv
echo "Making venv with $PYTHONBIN"
ENVDIR=env$VERSION
$PYTHONBIN -m venv ./$ENVDIR
source ./$ENVDIR/bin/activate

echo "Now python is here:"
which python

# install packages
pip install -q --upgrade pip setuptools auditwheel
pip install -q twine Cython pytest toml scikit-build
if [ "$(uname)" == "Darwin" ]; then
    # Mac version of auditwheel
    pip install -q delocate
fi
export PATH="$(python -m site --user-base)/bin:$PATH"

echo "With $PATH python is here:"
which python

# configure cvc5
echo "Configuring"
./configure.sh $CONFIG --python-bindings --name=build_wheel

# building wheel
echo "Building pycvc5 wheel"

pushd build_wheel
DISTDIR=dist$VERSION
VERSION_SUFFIX=$VERSION_SUFFIX python $DIR/contrib/packaging_python/build_wheel.py bdist_wheel -d $DISTDIR

cd $DISTDIR

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

rm -rf $DISTDIR
mv build_wheel/$DISTDIR .

#rm -rf build_wheel
