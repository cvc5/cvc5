# Packaging for PyPi

Generally, PyPi packages with binary components are packaged as
[wheels](https://packaging.python.org/en/latest/glossary/#term-Wheel).


## Linux wheels

Python wheels with C/C++ extensions need to be built on an old version of Linux
so that they are supported on many platforms. The standard approach is to use
the [manylinux](https://github.com/pypa/manylinux) Docker images as proposed in
[PEP-513](https://www.python.org/dev/peps/pep-0513/).

Most of the process for building wheels is automated by scripts in
`contrib/packaging_python/` and is usually done for releases automatically by
our CI.
**PyPi does not allow reuploading any wheels with the same version number.**
This means there is
only one shot per version number (and per Python version), so it should work and
be a release version.

To build the python wheel from you current build directory, simply run
`mk_wheel.py bdist_wheel -d dist` from the build directory.

### Building wheels with manylinux2014

The main script for building and uploading wheels is implemented in the
`package-python-wheel` action. It builds a Docker container that is a slightly
extended version of `manylinux2014` (see `manylinux2014/Dockerfile`), runs the `mk_clean_wheel.sh` script for every supported python version and finally collects and uploads the wheels.

The `mk_clean_wheel.sh`:

1. prepares the environment by creating and activating a proper python venv and installing some packages;
2. configures cvc5 appropriately using the `mk_build_dir.py` script, which makes sure that the venv python version is used;
3. builds cvc5 and the python extension via the `mk_wheel.py` script;
4. postprocesses the wheel (with `auditwheel`) and moves it out of the build folder.


## Uploading to PyPi

To upload a wheel to test PyPi,

    twine upload --repository testpypi -u $USERNAME -p $PASSWORD PATH_TO_WHEEL

Note that you will need a TestPyPi login. Once it has been uploaded, you can
test (from anywhere, not just the container) that the wheel works by installing
it from the TestPyPi repository.

```
python3 -m pip install --index-url https://test.pypi.org/simple/ pycvc5==<cvc5 version number>
python3 -c "import pycvc5; solver = pycvc5.Solver(); print(solver.getIntegerSort())"
```

You can remove the repository argument from the upload command to upload to
real PyPi.

## What goes on within the Docker container

### Setup

Compared to `manylinux2014`, the container comes with `ccache` and some cvc5
dependencies preinstalled. Additionally, we set up appropriate symlinks so that
`ccache` is used with the standard C and C++ compilers (`cc`, `c++`, `gcc`, `g++`).

The idea is to mount a cvc5 checkout into the Docker container at `/home/pycvc5`.
This way, we don't need to care about cloning cvc5 within Docker and the `ccache` cache is automatically stored persistently outside of the container.

### Building

To build the wheel for a specific python version, simply run `mk_clean_wheel.sh` within the docker container, and pass it the python binary it shall use (`/opt/python/cp<something>/bin/python`) and options to the cvc5 configure script (usually something like `production --auto-download`).
The script will create a new build folder (`build_wheel`), configure and build cvc5 accordingly and store the wheel within a `wheel-<version>` folder.

### Testing

From within Docker, you can test a wheel as follows: to ensure that the `cvc5`
library is linked correctly (and not looking at a local path). To do this,
start from the top-level `cvc5` directory and run the following:
```
# delete build directory to get rid of local library
rm -r build
# start virtualenv
source ./env<Python version>/bin/activate
# install the wheel
pip install <path to wheel for this Python version>
# run a small example to make sure it works
python3 -c "import pycvc5; solver = pycvc5.Solver(); print(solver.getIntegerSort())"
```

### Test PyPi

In addition to the local test described above, you can do a test upload to
[TestPyPi](https://packaging.python.org/guides/using-testpypi/). To do this
run the following after building the wheel:
```
# start the virtualenv for this version (twine was installed here)
source ./env<Python version>/bin/activate
# upload to Test PyPi
twine upload --repository testpypi <path to wheel>
```

Note that you will need a TestPyPi login. Once it has been uploaded, you can
test (from anywhere, not just the container) that the wheel works by installing
it from the TestPyPi repository.

```
python3 -m pip install --index-url https://test.pypi.org/simple/ pycvc5==<cvc5 version number>
python3 -c "import pycvc5; solver = pycvc5.Solver(); print(solver.getIntegerSort())"
```

### Upload to PyPi

Once you are certain this wheel file is ready, you can upload it to PyPi. Note,
you will need a login for PyPi (this is separate from the TestPyPi login). The
steps are almost identical to the TestPyPi upload:
```
# start virtualenv where twine was installed for this Python version
source ./env<Python version>
# upload to PyPi with twine (be sure this ready!!)
twine upload <wheel file>
```

Once the `.whl` has been built, you should be able to upload it from anywhere.
