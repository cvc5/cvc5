#!/bin/bash

DIR=$(pwd)

PYTHONBIN=$1
CONFIG="$2"
VERSION=$($PYTHONBIN -c "import sys; print(sys.version.split()[0])")

# setup and activate venv
echo "Making venv"
ENVDIR=env$VERSION
$PYTHONBIN -m venv ./$ENVDIR
source ./$ENVDIR/bin/activate

# install packages
pip install --upgrade pip setuptools auditwheel
pip install twine Cython pytest toml scikit-build
if [ "$(uname)" == "Darwin" ]; then
    # Mac version of auditwheel
    pip install delocate
fi

# configure cvc5
echo "Configuring"
./configure.sh $CONFIG --python-bindings --name=build_wheel

# building wheel
echo "Building pycvc5 wheel"

pushd build_wheel
DISTDIR=dist$VERSION
VERSION_SUFFIX=$VERSION_SUFFIX python3 $DIR/contrib/packaging_python/build_wheel.py bdist_wheel -d $DISTDIR

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

cd $DIR

if [ -f $DIR/$DISTDIR/wheelhouse/*.whl ]; then
    # the fixed up wheel is in the wheelhouse directory
    # delete the old one
    rm ./$DISTDIR/*.whl

    FILES=( "$DIR/$DISTDIR/wheelhouse/*.whl" )
    WHEELFILE="${files[0]}"
    echo ""
    echo "It appears the pycvc5 wheel was built successfully"
    echo "It's recommended to test it locally, by deleting the library"
    echo "e.g. rm -r ./build"
    echo "Then installing and making sure the library was bundled"
    echo "  with the wheel correctly."
    echo "pip install $WHEELFILE"
    echo "python3 -c 'import pycvc5; solver=pycvc5.Solver(); print(solver.getIntegerSort())'"
    echo "If it seems fine, you can upload to PyPi with:"
    echo "        twine upload $WHEELFILE"
    echo "or to TestPyPi with "
    echo "        twine upload --repository testpypi $WHEELFILE"
fi

