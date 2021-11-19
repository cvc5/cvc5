#!/bin/bash

DIR=$(pwd)

usage()
{
    echo "$0 <python3 binary>"
    echo "Builds wheels and places in dist<python version>"
}

if [[ "$1" == "--help" ]]; then
    usage
    exit 1
fi

PYTHONBIN=$1
VERSION=$($PYTHONBIN -c "import sys; print(sys.version.split()[0])")
CURDIR=$(basename $DIR)

if [[ "$CURDIR" != "cvc5" ]]; then
    echo "Expecting to be run from cvc5 directory but actually run from $DIR"
    exit 1
fi

ENVDIR=env$VERSION
$PYTHONBIN -m venv ./$ENVDIR
source ./$ENVDIR/bin/activate

pip install --upgrade pip
pip install --upgrade setuptools

pip install twine Cython pytest toml scikit-build

if [ "$(uname)" == "Darwin" ]; then
    # Mac version of auditwheel
    pip install delocate
fi

echo "Building pycvc5 wheel"
DISTDIR=dist$VERSION
VERSION_SUFFIX=$VERSION_SUFFIX python3 ./contrib/packaging_python/build_wheel.py bdist_wheel -d $DISTDIR
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

