Python API
========================

.. only:: not bindings_python

    .. warning::

        This documentation was built while python bindings were disabled. This part of the documentation is likely either empty or outdated. Please enable :code:`BUILD_BINDINGS_PYTHON` in :code:`cmake` and build the documentation again.

cvc5 offers two separate APIs for Python users.
The :doc:`base Python API <base/python>` is an almost exact copy of the :doc:`C++ API <../cpp/cpp>`.
Alternatively, the :doc:`pythonic API <pythonic/pythonic>` is a more pythonic API that aims to be fully compatible with `Z3s Python API <https://z3prover.github.io/api/html/namespacez3py.html>`_ while adding functionality that Z3 does not support.

.. toctree::
    :maxdepth: 1

    pythonic/pythonic
    base/python


Which Python API should I use?
------------------------------

If you are a new user, or already have an application that uses Z3's python API, use the :doc:`pythonic API <pythonic/pythonic>`.

If you would like a more feature-complete---yet verbose---python API, with the ability to do almost everything that the cpp API allows, use the :doc:`base Python API <base/python>`.

You can compare examples using the two APIs by visiting the :doc:`examples page <../../examples/quickstart>`.


Installation (x86-64 variants of Linux and macOS)
------------

The base and pythonic Python API can be installed via `pip` as follows:

.. code:: bash

  pip install cvc5


Installation (ARM64 variants of Linux and macOS)
------------

For ARM64-based machines (including Apple computers with M1 and M2 chips), the base and the pythonic Python API can be installed from source.
Before building and installing, the following dependencies should be installed, using `brew` and `pip`:

.. code:: bash

  brew install cmake python cython gmp java
  pip3 install toml scikit-build pyparsing


Then `cvc5` can be installed from source as follows:

.. code:: bash

  git clone git@github.com:cvc5/cvc5.git
  cd cvc5
  ./configure.sh --python-bindings --auto-download
  cd build
  make -j cvc5_python_api
  export PYTHONPATH=“<path-to-local-cvc5-repo>/build/src/api/python/:$PYTHONPATH”

And to make sure that it works:

.. code:: bash

  python3
  import cvc5
