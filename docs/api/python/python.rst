Python API Documentation
========================

.. toctree::
    :maxdepth: 1
    :hidden:

    z3py compatibility API <z3compat/z3compat>
    regular Python API <regular/python>

.. only:: not bindings_python

    .. warning::

        This documentation was built while python bindings were disabled. This part of the documentation is likely either empty or outdated. Please enable :code:`BUILD_BINDINGS_PYTHON` in :code:`cmake` and build the documentation again.

cvc5 offers two separate APIs for Python users.
The :doc:`regular Python API <regular/python>` is an almost exact copy of the :doc:`C++ API <../cpp/cpp>`.
Alternatively, the :doc:`z3py compatibility API <z3compat/z3compat>` is a more pythonic API that aims to be fully compatible with `Z3s Python API <https://z3prover.github.io/api/html/namespacez3py.html>`_ while adding functionality that Z3 does not support.


Which Python API should I use?
------------------------------

Most of the time, use the :doc:`z3py compatibility API <z3compat/z3compat>`.
