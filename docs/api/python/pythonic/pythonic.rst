Pythonic API
=========================================

.. only:: not bindings_python

    .. warning::

        This documentation was built while python bindings were disabled. This part of the documentation is likely either empty or outdated. Please enable :code:`BUILD_BINDINGS_PYTHON` in :code:`cmake` and build the documentation again.


This API is missing some features from cvc5 and Z3Py.

It does not (currently) support these cvc5 features:

* The theories of strings, sequences and bags
* unsatisfiable cores
* syntax-guided synthesis (SyGuS)

It does not (currently) support the following features of Z3Py:

* Patterns for quantifier instantiation
* Pseudo-boolean counting constraints: AtMost, AtLeast, ...
* Special relation classes: PartialOrder, LinearOrder, ...
* HTML integration
* Hooks for user-defined propagation and probing
* Fixedpoint API
* Finite domains
* SMT2 file parsing

.. toctree::
    :maxdepth: 2

    quickstart
    boolean
    arith
    array
    bitvec
    dt
    fp
    set
    quant
    solver
    internals
