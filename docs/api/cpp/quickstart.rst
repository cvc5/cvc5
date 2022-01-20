Quickstart Guide
================

First, create a cvc5 :cpp:class:`Solver <cvc5::api::Solver>` instance:

.. literalinclude:: ../../../examples/api/cpp/quickstart.cpp
     :language: cpp
     :lines: 27

We will ask the solver to produce models and unsat cores in the following,
and for this we have to enable the following options.

.. literalinclude:: ../../../examples/api/cpp/quickstart.cpp
     :language: cpp
     :lines: 31-32

Next we set the logic.
The simplest way to set a logic for the solver is to choose "ALL".
This enables all logics in the solver.
Alternatively, ``"QF_ALL"`` enables all logics without quantifiers.
To optimize the solver's behavior for a more specific logic,
use the logic name, e.g. ``"QF_BV"`` or ``"QF_AUFBV"``.

.. literalinclude:: ../../../examples/api/cpp/quickstart.cpp
     :language: cpp
     :lines: 41

In the following, we will define constraints of reals and integers.
For this, we first query the solver for the corresponding sorts.

.. literalinclude:: ../../../examples/api/cpp/quickstart.cpp
     :language: cpp
     :lines: 45-46

Now, we create two constants ``x`` and ``y`` of sort ``Real``,
and two constants ``a`` and ``b`` of sort ``Integer``.
Notice that these are *symbolic* constants, but not actual values.

.. literalinclude:: ../../../examples/api/cpp/quickstart.cpp
     :language: cpp
     :lines: 51-54

We define the following constraints regarding ``x`` and ``y``:

.. math::

  (0 < x) \wedge (0 < y) \wedge (x + y < 1) \wedge (x \leq y)

We construct the required terms and assert them as follows:

.. literalinclude:: ../../../examples/api/cpp/quickstart.cpp
     :language: cpp
     :lines: 64-88

Now we check if the asserted formula is satisfiable, that is, we check if
there exist values of sort ``Real`` for ``x`` and ``y`` that satisfy all
the constraints.

.. literalinclude:: ../../../examples/api/cpp/quickstart.cpp
     :language: cpp
     :lines: 92

The result we get from this satisfiability check is either ``sat``, ``unsat``
or ``unknown``.
It's status can be queried via
:cpp:func:`cvc5::api::Result::isSat`,
:cpp:func:`cvc5::api::Result::isUnsat` and
:cpp:func:`cvc5::api::Result::isSatUnknown`.
Alternatively, it can also be printed.

.. literalinclude:: ../../../examples/api/cpp/quickstart.cpp
     :language: cpp
     :lines: 96-97

This will print:

.. code:: text

  expected: sat
  result: sat

Now, we query the solver for the values for ``x`` and ``y`` that satisfy
the constraints.

.. literalinclude:: ../../../examples/api/cpp/quickstart.cpp
     :language: cpp
     :lines: 100-101

It is also possible to get values for terms that do not appear in the original
formula.

.. literalinclude:: ../../../examples/api/cpp/quickstart.cpp
     :language: cpp
     :lines: 105-106

We can retrieve the string representation of these values as follows.

.. literalinclude:: ../../../examples/api/cpp/quickstart.cpp
     :language: cpp
     :lines: 109-115

This will print the following:

.. code:: text

  value for x: 1/6
  value for y: 1/6
  value for x - y: 0.0

We can convert these values to C++ types.

.. literalinclude:: ../../../examples/api/cpp/quickstart.cpp
     :language: cpp
     :lines: 117-124

Another way to independently compute the value of ``x - y`` would be to
perform the (rational) arithmetic manually.
However, for more complex terms, it is easier to let the solver do the
evaluation.

.. literalinclude:: ../../../examples/api/cpp/quickstart.cpp
     :language: cpp
     :lines: 130-143

This will print:

.. code:: text

  computed correctly

Next, we will check satisfiability of the same formula,
only this time over integer variables ``a`` and ``b``.
For this, we first reset the assertions added to the solver.

.. literalinclude:: ../../../examples/api/cpp/quickstart.cpp
     :language: cpp
     :lines: 149

Next, we assert the same assertions as above, but with integers.
This time, we inline the construction of terms
to the assertion command.

.. literalinclude:: ../../../examples/api/cpp/quickstart.cpp
     :language: cpp
     :lines: 154-158

Now, we check whether the revised assertion is satisfiable.

.. literalinclude:: ../../../examples/api/cpp/quickstart.cpp
     :language: cpp
     :lines: 161, 164-165

This time the asserted formula is unsatisfiable:

.. code:: text

  expected: unsat
  result: unsat

We can query the solver for an unsatisfiable core, that is, a subset
of the assertions that is already unsatisfiable.

.. literalinclude:: ../../../examples/api/cpp/quickstart.cpp
     :language: cpp
     :lines: 169-175

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
    <examples>/api/cpp/quickstart.cpp
    <examples>/api/java/QuickStart.java
    <z3pycompat>/test/pgms/example_quickstart.py
    <examples>/api/python/quickstart.py
    <examples>/api/smtlib/quickstart.smt2
