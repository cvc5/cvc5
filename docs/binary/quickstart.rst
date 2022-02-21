Quickstart Guide
================

The primary input language for cvc5 is
`SMT-LIB v2 <http://smtlib.cs.uiowa.edu/language.shtml>`_.
We give a short explanation of the SMT-LIB v2 quickstart
example here.

First, we set the logic.
The simplest way to set a logic for the solver is to choose "ALL".
This enables all logics in the solver.
Alternatively, ``"QF_ALL"`` enables all logics without quantifiers.
To optimize the solver's behavior for a more specific logic,
use the logic name, e.g. ``"QF_BV"`` or ``"QF_AUFBV"``.

.. literalinclude:: ../../examples/api/smtlib/quickstart.smt2
     :language: smtlib
     :lines: 1

We will ask the solver to produce models and unsat cores in the following,
and for this we have to enable the following options.
Furthermore, we enable incremental solving so that we can use the
``(reset-assertions)`` command later on.

.. literalinclude:: ../../examples/api/smtlib/quickstart.smt2
     :language: smtlib
     :lines: 2-6

Now, we create two constants ``x`` and ``y`` of sort ``Real``.
Notice that these are *symbolic* constants, but not actual values.

.. literalinclude:: ../../examples/api/smtlib/quickstart.smt2
     :language: smtlib
     :lines: 8-10

We define the following constraints regarding ``x`` and ``y``:

.. math::

  (0 < x) \wedge (0 < y) \wedge (x + y < 1) \wedge (x \leq y)

We assert them as follows. Notice that in SMT-LIB v2, terms are written in prefix notation, e.g., we write `(+ x y)` instead of `(x + y)`.

.. literalinclude:: ../../examples/api/smtlib/quickstart.smt2
     :language: smtlib
     :lines: 12-22

Now we check if the asserted formula is satisfiable, that is, we check if
there exist values of sort ``Real`` for ``x`` and ``y`` that satisfy all
the constraints.

.. literalinclude:: ../../examples/api/smtlib/quickstart.smt2
     :language: smtlib
     :lines: 24

The result we get from this satisfiability check is either ``sat``, ``unsat``
or ``unknown``, and it is printed to standard output.
In this case, it will print ``sat``.

Now, we query the solver for the values for ``x`` and ``y`` that satisfy
the constraints.
It is also possible to get values for terms that do not appear in the original
formula.

.. literalinclude:: ../../examples/api/smtlib/quickstart.smt2
     :language: smtlib
     :lines: 25-26

This will print the values of `x`, `y`, and `x-y`, in a key-value format `(<term> <value>)` one after the other:

.. code:: text

  ((x (/ 1 6)) (y (/ 1 6)) ((- x y) 0.0))

Next, we will check satisfiability of the same formula,
only this time over integer variables ``a`` and ``b``.
For this, we first reset the assertions added to the solver and declare fresh
integer variables ``a`` and ``b``.

.. literalinclude:: ../../examples/api/smtlib/quickstart.smt2
     :language: smtlib
     :lines: 28-32

Next, we assert the same assertions as above, but with integers.

.. literalinclude:: ../../examples/api/smtlib/quickstart.smt2
     :language: smtlib
     :lines: 33-36

Now, we check whether the revised query is satisfiable.

.. literalinclude:: ../../examples/api/smtlib/quickstart.smt2
     :language: smtlib
     :lines: 38

This time the asserted formula is unsatisfiable and ``unsat`` is printed.

We can query the solver for an unsatisfiable core, that is, a subset
of the assertions that is already unsatisfiable.

.. literalinclude:: ../../examples/api/smtlib/quickstart.smt2
     :language: smtlib
     :lines: 39

This will print:

.. code:: text
    
  (
  (< 0 a)
  (< 0 b)
  (< (+ a b) 1)
  )

Example
-------

.. api-examples::
    <examples>/api/smtlib/quickstart.smt2
    <examples>/api/cpp/quickstart.cpp
    <examples>/api/java/QuickStart.java
    <z3pycompat>/test/pgms/example_quickstart.py
    <examples>/api/python/quickstart.py
