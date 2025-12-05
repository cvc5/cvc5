Python API
==========

.. only:: not bindings_python

    .. warning::

        This documentation was built while python bindings were disabled. This part of the documentation is likely either empty or outdated. Please enable :code:`BUILD_BINDINGS_PYTHON` in :code:`cmake` and build the documentation again.

cvc5 offers two separate APIs for Python users.
The :doc:`base Python API <base/python>` is an almost exact copy of the
:doc:`C++ API <../cpp/cpp>`.
Alternatively, the :doc:`pythonic API <pythonic/pythonic>` is a more pythonic
API that aims to be fully compatible with `Z3s Python API
<https://z3prover.github.io/api/html/namespacez3py.html>`_ while adding
functionality that Z3 does not support.

.. toctree::
    :maxdepth: 1

    pythonic/pythonic
    base/python


Which Python API should I use?
------------------------------

If you are a new user, or already have an application that uses Z3's python
API, use the :doc:`pythonic API <pythonic/pythonic>`.
If you would like a more feature-complete---yet verbose---python API, with the
ability to do almost everything that the cpp API allows, use the :doc:`base
Python API <base/python>`.

You can compare examples using the two APIs by visiting the :doc:`examples page
<../../examples/quickstart>`.


Installation (from PyPi)
------------------------

The base and pythonic Python API can be installed via `pip` as follows:

.. code:: bash

  pip install cvc5


Installation (from source)
--------------------------

The base and pythonic Python API can also be installed from source following
these steps:

.. code:: bash

  git clone https://github.com/cvc5/cvc5.git
  cd cvc5
  ./configure.sh --python-bindings --auto-download
  cd build
  make # add -jN for parallel build using N threads
  make install

The last step installs both the cvc5 binary and the Python bindings.
If you want to install only the Python bindings, run the following
command instead of ``make install``:

.. code:: bash

  cmake --install . --component python-api

For Windows, the steps above must be executed in
a CLANG64 or CLANGARM64 environment with the required
dependencies installed
(see the :doc:`installation instructions <../../installation/installation>`).

Finally, you can make sure that it works by running:

.. code:: bash

  python3
  import cvc5
