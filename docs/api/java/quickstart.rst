Quickstart Guide
================

First, create a cvc5 `Solver <io/github/cvc5/api/Solver.html>`_
instance using try with resources:

.. code-block:: java

     try (Solver solver = new Solver())
     {
       /** write your code here */
     }

To produce models and unsat cores, we have to enable the following options.

.. literalinclude:: ../../../examples/api/java/QuickStart.java
     :language: java
     :lines: 32-33
     :dedent: 6

Next we set the logic.
The simplest way to set a logic for the solver is to choose ``"ALL"``.
This enables all logics in the solver.
Alternatively, ``"QF_ALL"`` enables all logics without quantifiers.
To optimize the solver's behavior for a more specific logic,
use the logic name, e.g. ``"QF_BV"`` or ``"QF_AUFBV"``.

.. literalinclude:: ../../../examples/api/java/QuickStart.java
     :language: java
     :lines: 42
     :dedent: 6

In the following, we will define real and integer constraints.
For this, we first query the solver for the corresponding sorts.

.. literalinclude:: ../../../examples/api/java/QuickStart.java
     :language: java
     :lines: 46-47
     :dedent: 6

Now, we create two constants ``x`` and ``y`` of sort ``Real``,
and two constants ``a`` and ``b`` of sort ``Integer``.
Notice that these are *symbolic* constants, not actual values.

.. literalinclude:: ../../../examples/api/java/QuickStart.java
     :language: java
     :lines: 52-55
     :dedent: 6

We define the following constraints regarding ``x`` and ``y``:

.. math::

  (0 < x) \wedge (0 < y) \wedge (x + y < 1) \wedge (x \leq y)

We construct the required terms and assert them as follows:

.. literalinclude:: ../../../examples/api/java/QuickStart.java
     :language: java
     :lines: 65-89
     :dedent: 6

Now we check if the asserted formula is satisfiable, that is, we check if
there exist values of sort ``Real`` for ``x`` and ``y`` that satisfy all
the constraints.

.. literalinclude:: ../../../examples/api/java/QuickStart.java
     :language: java
     :lines: 93
     :dedent: 6

The result we get from this satisfiability check is either ``sat``, ``unsat``
or ``unknown``.
It's status can be queried via
`Result.isSat <io/github/cvc5/api/Result.html#isSat()>`_,
`Result.isUnsat <io/github/cvc5/api/Result.html#isUnsat()>`_ and
`Result.isSatUnknown <io/github/cvc5/api/Result.html#isSatUnknown()>`_.
Alternatively, it can also be printed.

.. literalinclude:: ../../../examples/api/java/QuickStart.java
     :language: java
     :lines: 97-98
     :dedent: 6

This will print:

.. code:: text

  expected: sat
  result: sat

Now, we query the solver for the values for ``x`` and ``y`` that satisfy
the constraints.

.. literalinclude:: ../../../examples/api/java/QuickStart.java
     :language: java
     :lines: 101-102
     :dedent: 6

It is also possible to get values for terms that do not appear in the original
formula.

.. literalinclude:: ../../../examples/api/java/QuickStart.java
     :language: java
     :lines: 106-107
     :dedent: 6

We can convert these values to Java types.

.. literalinclude:: ../../../examples/api/java/QuickStart.java
     :language: java
     :lines: 109-116
     :dedent: 6

Another way to independently compute the value of ``x - y`` would be to
perform the (rational) arithmetic manually.
However, for more complex terms, it is easier to let the solver do the
evaluation.

.. literalinclude:: ../../../examples/api/java/QuickStart.java
     :language: java
     :lines: 122-134
     :dedent: 6

This will print:

.. code:: text

  computed correctly

Next, we will check satisfiability of the same formula,
only this time over integer variables ``a`` and ``b``.
For this, we first reset the assertions added to the solver.

.. literalinclude:: ../../../examples/api/java/QuickStart.java
     :language: java
     :lines: 140
     :dedent: 6

Next, we assert the same assertions as above, but with integers.
This time, we inline the construction of terms
in the assertion command.

.. literalinclude:: ../../../examples/api/java/QuickStart.java
     :language: java
     :lines: 145-149
     :dedent: 6

Now, we check whether the revised assertion is satisfiable.

.. literalinclude:: ../../../examples/api/java/QuickStart.java
     :language: java
     :lines: 152-156
     :dedent: 6

This time the asserted formula is unsatisfiable:

.. code:: text

  expected: unsat
  result: unsat

We can query the solver for an unsatisfiable core, that is, a subset
of the assertions that is already unsatisfiable.

.. literalinclude:: ../../../examples/api/java/QuickStart.java
     :language: java
     :lines: 160-166
     :dedent: 6

This will print:

.. code:: text

  unsat core size: 3
  unsat core:
  (< 0 a)
  (< 0 b)
  (< (+ a b) 1)

Example
-------

.. api-examples::
    <examples>/api/java/QuickStart.java
    <examples>/api/cpp/quickstart.cpp
    <z3pycompat>/test/pgms/example_quickstart.py
    <examples>/api/python/quickstart.py
    <examples>/api/smtlib/quickstart.smt2
