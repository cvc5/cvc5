Quickstart Guide
================

First, create a cvc5 `Solver <io/github/cvc5/api/Solver.html>`_
instance:

.. code-block:: java

     Solver solver = new Solver();

To produce models and unsat cores, we have to enable the following options.

.. literalinclude:: ../../../examples/api/java/QuickStart.java
   :language: java
   :dedent: 6
   :start-after: docs-java-quickstart-1 start
   :end-before: docs-java-quickstart-1 end

Next we set the logic.
The simplest way to set a logic for the solver is to choose ``"ALL"``.
This enables all logics in the solver.
Alternatively, ``"QF_ALL"`` enables all logics without quantifiers.
To optimize the solver's behavior for a more specific logic,
use the logic name, e.g. ``"QF_BV"`` or ``"QF_AUFBV"``.

.. literalinclude:: ../../../examples/api/java/QuickStart.java
   :language: java
   :dedent: 6
   :start-after: docs-java-quickstart-2 start
   :end-before: docs-java-quickstart-2 end

In the following, we will define real and integer constraints.
For this, we first query the solver for the corresponding sorts.

.. literalinclude:: ../../../examples/api/java/QuickStart.java
   :language: java
   :dedent: 6
   :start-after: docs-java-quickstart-3 start
   :end-before: docs-java-quickstart-3 end

Now, we create two constants ``x`` and ``y`` of sort ``Real``,
and two constants ``a`` and ``b`` of sort ``Integer``.
Notice that these are *symbolic* constants, not actual values.

.. literalinclude:: ../../../examples/api/java/QuickStart.java
   :language: java
   :dedent: 6
   :start-after: docs-java-quickstart-4 start
   :end-before: docs-java-quickstart-4 end

We define the following constraints regarding ``x`` and ``y``:

.. math::

  (0 < x) \wedge (0 < y) \wedge (x + y < 1) \wedge (x \leq y)

We construct the required terms and assert them as follows:

.. literalinclude:: ../../../examples/api/java/QuickStart.java
   :language: java
   :dedent: 6
   :start-after: docs-java-quickstart-5 start
   :end-before: docs-java-quickstart-5 end

Now we check if the asserted formula is satisfiable, that is, we check if
there exist values of sort ``Real`` for ``x`` and ``y`` that satisfy all
the constraints.

.. literalinclude:: ../../../examples/api/java/QuickStart.java
   :language: java
   :dedent: 6
   :start-after: docs-java-quickstart-6 start
   :end-before: docs-java-quickstart-6 end

The result we get from this satisfiability check is either ``sat``, ``unsat``
or ``unknown``.
It's status can be queried via
`Result.isSat <io/github/cvc5/api/Result.html#isSat()>`_,
`Result.isUnsat <io/github/cvc5/api/Result.html#isUnsat()>`_ and
`Result.isSatUnknown <io/github/cvc5/api/Result.html#isSatUnknown()>`_.
Alternatively, it can also be printed.

.. literalinclude:: ../../../examples/api/java/QuickStart.java
   :language: java
   :dedent: 6
   :start-after: docs-java-quickstart-7 start
   :end-before: docs-java-quickstart-7 end

This will print:

.. code:: text

  expected: sat
  result: sat

Now, we query the solver for the values for ``x`` and ``y`` that satisfy
the constraints.

.. literalinclude:: ../../../examples/api/java/QuickStart.java
   :language: java
   :dedent: 6
   :start-after: docs-java-quickstart-8 start
   :end-before: docs-java-quickstart-8 end

It is also possible to get values for terms that do not appear in the original
formula.

.. literalinclude:: ../../../examples/api/java/QuickStart.java
   :language: java
   :dedent: 6
   :start-after: docs-java-quickstart-9 start
   :end-before: docs-java-quickstart-9 end

We can convert these values to Java types.

.. literalinclude:: ../../../examples/api/java/QuickStart.java
   :language: java
   :dedent: 6
   :start-after: docs-java-quickstart-10 start
   :end-before: docs-java-quickstart-10 end

Another way to independently compute the value of ``x - y`` would be to
perform the (rational) arithmetic manually.
However, for more complex terms, it is easier to let the solver do the
evaluation.

.. literalinclude:: ../../../examples/api/java/QuickStart.java
   :language: java
   :dedent: 6
   :start-after: docs-java-quickstart-11 start
   :end-before: docs-java-quickstart-11 end

This will print:

.. code:: text

  computed correctly

Next, we will check satisfiability of the same formula,
only this time over integer variables ``a`` and ``b``.
For this, we first reset the assertions added to the solver.

.. literalinclude:: ../../../examples/api/java/QuickStart.java
   :language: java
   :dedent: 6
   :start-after: docs-java-quickstart-12 start
   :end-before: docs-java-quickstart-12 end

Next, we assert the same assertions as above, but with integers.
This time, we inline the construction of terms
in the assertion command.

.. literalinclude:: ../../../examples/api/java/QuickStart.java
   :language: java
   :dedent: 6
   :start-after: docs-java-quickstart-13 start
   :end-before: docs-java-quickstart-13 end

Now, we check whether the revised assertion is satisfiable.

.. literalinclude:: ../../../examples/api/java/QuickStart.java
   :language: java
   :dedent: 6
   :start-after: docs-java-quickstart-14 start
   :end-before: docs-java-quickstart-14 end

This time the asserted formula is unsatisfiable:

.. code:: text

  expected: unsat
  result: unsat

We can query the solver for an unsatisfiable core, that is, a subset
of the assertions that is already unsatisfiable.

.. literalinclude:: ../../../examples/api/java/QuickStart.java
   :language: java
   :dedent: 6
   :start-after: docs-java-quickstart-15 start
   :end-before: docs-java-quickstart-15 end

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
    <pythonicapi>/test/pgms/example_quickstart.py
    <examples>/api/python/quickstart.py
    <examples>/api/smtlib/quickstart.smt2
