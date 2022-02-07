Quickstart Guide
================

First, create a cvc5 solver instance:

.. literalinclude:: ../../../../examples/api/python/quickstart.py
     :language: python
     :lines: 22

We will ask the solver to produce models and unsat cores in the following,
and for this we have to enable the following options.

.. literalinclude:: ../../../../examples/api/python/quickstart.py
     :language: python
     :lines: 26-27

Next we set the logic.
The simplest way to set a logic for the solver is to choose ``"ALL"``.
This enables all logics in the solver.
Alternatively, ``"QF_ALL"`` enables all logics without quantifiers.
To optimize the solver's behavior for a more specific logic,
use the logic name, e.g. ``"QF_BV"`` or ``"QF_AUFBV"``.

.. literalinclude:: ../../../../examples/api/python/quickstart.py
     :language: python
     :lines: 36

In the following, we will define constraints of reals and integers.
For this, we first query the solver for the corresponding sorts.

.. literalinclude:: ../../../../examples/api/python/quickstart.py
     :language: python
     :lines: 40-41

Now, we create two constants ``x`` and ``y`` of sort ``Real``,
and two constants ``a`` and ``b`` of sort ``Integer``.
Notice that these are *symbolic* constants, but not actual values.

.. literalinclude:: ../../../../examples/api/python/quickstart.py
     :language: python
     :lines: 46-49

We define the following constraints regarding ``x`` and ``y``:

.. math::

  (0 < x) \wedge (0 < y) \wedge (x + y < 1) \wedge (x \leq y)

We construct the required terms and assert them as follows:

.. literalinclude:: ../../../../examples/api/python/quickstart.py
     :language: python
     :lines: 59-81

Now we check if the asserted formula is satisfiable, that is, we check if
there exist values of sort ``Real`` for ``x`` and ``y`` that satisfy all
the constraints.

.. literalinclude:: ../../../../examples/api/python/quickstart.py
     :language: python
     :lines: 85

The result we get from this satisfiability check is either ``sat``, ``unsat``
or ``unknown``.
It's status can be queried via `isSat`, `isUnsat` and `isSatUnknown` functions.
Alternatively, it can also be printed.

.. literalinclude:: ../../../../examples/api/python/quickstart.py
     :language: python
     :lines: 89-90

This will print:

.. code:: text

  expected: sat
  result: sat

Now, we query the solver for the values for ``x`` and ``y`` that satisfy
the constraints.

.. literalinclude:: ../../../../examples/api/python/quickstart.py
     :language: python
     :lines: 93-94

It is also possible to get values for terms that do not appear in the original
formula.

.. literalinclude:: ../../../../examples/api/python/quickstart.py
     :language: python
     :lines: 98-99

We can retrieve the Python representation of these values as follows.

.. literalinclude:: ../../../../examples/api/python/quickstart.py
     :language: python
     :lines: 102-108

This will print the following:

.. code:: text

  value for x: 1/6
  value for y: 1/6
  value for x - y: 0

Another way to independently compute the value of ``x - y`` would be to
use the Python minus operator instead of asking the solver.
However, for more complex terms, it is easier to let the solver do the
evaluation.

.. literalinclude:: ../../../../examples/api/python/quickstart.py
     :language: python
     :lines: 114-118

This will print:

.. code:: text

  computed correctly

Next, we will check satisfiability of the same formula,
only this time over integer variables ``a`` and ``b``.
For this, we first reset the assertions added to the solver.

.. literalinclude:: ../../../../examples/api/python/quickstart.py
     :language: python
     :lines: 130

Next, we assert the same assertions as above, but with integers.
This time, we inline the construction of terms
to the assertion command.

.. literalinclude:: ../../../../examples/api/python/quickstart.py
     :language: python
     :lines: 135-139

Now, we check whether the revised assertion is satisfiable.

.. literalinclude:: ../../../../examples/api/python/quickstart.py
     :language: python
     :lines: 142, 145-146

This time the asserted formula is unsatisfiable:

.. code:: text

  expected: unsat
  result: unsat

We can query the solver for an unsatisfiable core, that is, a subset
of the assertions that is already unsatisfiable.

.. literalinclude:: ../../../../examples/api/python/quickstart.py
     :language: python
     :lines: 150-152

This will print:

.. code:: text

  unsat core size: 3
  unsat core: [(< 0 a), (< 0 b), (< (+ a b) 1)]

Example
-------

.. api-examples::
    <examples>/api/python/quickstart.py
    <examples>/api/cpp/quickstart.cpp
    <examples>/api/java/QuickStart.java
    <z3pycompat>/test/pgms/example_quickstart.py
    <examples>/api/smtlib/quickstart.smt2
