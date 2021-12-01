Quickstart Guide
================

First, create a cvc5 `Solver <io/github/cvc5/api/Solver.html>`_ instance using try with resources:

.. code-block:: java

     try (Solver solver = new Solver())
     {
       /** write your code here */
     }

We will ask the solver to produce models and unsat cores in the following,
and for this we have to enable the following options.

.. code-block:: java

     solver.setOption("produce-models", "true");
     solver.setOption("produce-unsat-cores", "true");

Next we set the logic.
The simplest way to set a logic for the solver is to choose "ALL".
This enables all logics in the solver.
Alternatively, ``"QF_ALL"`` enables all logics without quantifiers.
To optimize the solver's behavior for a more specific logic,
use the logic name, e.g. ``"QF_BV"`` or ``"QF_AUFBV"``.

.. code-block:: java

     solver.setLogic("ALL");

In the following, we will define constraints of reals and integers.
For this, we first query the solver for the corresponding sorts.

.. code-block:: java

     Sort realSort = solver.getRealSort();
     Sort intSort = solver.getIntegerSort();

Now, we create two constants ``x`` and ``y`` of sort ``Real``,
and two constants ``a`` and ``b`` of sort ``Integer``.
Notice that these are *symbolic* constants, but not actual values.

.. code-block:: java

     Term x = solver.mkConst(realSort, "x");
     Term y = solver.mkConst(realSort, "y");
     Term a = solver.mkConst(intSort, "a");
     Term b = solver.mkConst(intSort, "b");

We define the following constraints regarding ``x`` and ``y``:

.. math::

  (0 < x) \wedge (0 < y) \wedge (x + y < 1) \wedge (x \leq y)

We construct the required terms and assert them as follows:

.. code-block:: java

     // Formally, constraints are also terms. Their sort is Boolean.
     // We will construct these constraints gradually,
     // by defining each of their components.
     // We start with the constant numerals 0 and 1:
     Term zero = solver.mkReal(0);
     Term one = solver.mkReal(1);

     // Next, we construct the term x + y
     Term xPlusY = solver.mkTerm(Kind.PLUS, x, y);

     // Now we can define the constraints.
     // They use the operators +, <=, and <.
     // In the API, these are denoted by PLUS, LEQ, and LT.
     // A list of available operators is available in:
     // src/api/cpp/cvc5_kind.h
     Term constraint1 = solver.mkTerm(Kind.LT, zero, x);
     Term constraint2 = solver.mkTerm(Kind.LT, zero, y);
     Term constraint3 = solver.mkTerm(Kind.LT, xPlusY, one);
     Term constraint4 = solver.mkTerm(Kind.LEQ, x, y);

Now we check if the asserted formula is satisfiable, that is, we check if
there exist values of sort ``Real`` for ``x`` and ``y`` that satisfy all
the constraints.

.. code-block:: java

     Result r1 = solver.checkSat();

The result we get from this satisfiability check is either ``sat``, ``unsat``
or ``unknown``.
It's status can be queried via
`Result.isSat <io/github/cvc5/api/Result.html#isSat()>`_,
`Result.isUnsat <io/github/cvc5/api/Result.html#isUnsat()>`_ and
`Result.isSatUnknown <io/github/cvc5/api/Result.html#isSatUnknown()>`_.
Alternatively, it can also be printed.

.. code-block:: java

     System.out.println("expected: sat");
     System.out.println("result: " + r1);

This will print:

.. code:: text

  expected: sat
  result: sat

Now, we query the solver for the values for ``x`` and ``y`` that satisfy
the constraints.

.. code-block:: java

     Term xVal = solver.getValue(x);
     Term yVal = solver.getValue(y);

It is also possible to get values for terms that do not appear in the original
formula.

.. code-block:: java

     Term xMinusY = solver.mkTerm(Kind.MINUS, x, y);
     Term xMinusYVal = solver.getValue(xMinusY);

We can convert these values to Java types.

.. code-block:: java

     // Further, we can convert the values to java types
     Pair<BigInteger, BigInteger> xPair = xVal.getRealValue();
     Pair<BigInteger, BigInteger> yPair = yVal.getRealValue();
     Pair<BigInteger, BigInteger> xMinusYPair = xMinusYVal.getRealValue();
     System.out.println("value for x: " + xPair.first + "/" + xPair.second);
     System.out.println("value for y: " + yPair.first + "/" + yPair.second);
     System.out.println("value for x - y: " + xMinusYPair.first + "/" + xMinusYPair.second);

Another way to independently compute the value of ``x - y`` would be to
perform the (rational) arithmetic manually.
However, for more complex terms, it is easier to let the solver do the
evaluation.

.. code-block:: java

     Pair<BigInteger, BigInteger> xMinusYComputed =
          new Pair(xPair.first.multiply(yPair.second).subtract(xPair.second.multiply(yPair.first)),
              xPair.second.multiply(yPair.second));
     BigInteger g = xMinusYComputed.first.gcd(xMinusYComputed.second);
     xMinusYComputed = new Pair(xMinusYComputed.first.divide(g), xMinusYComputed.second.divide(g));
     if (xMinusYComputed.equals(xMinusYPair))
     {
       System.out.println("computed correctly");
     }
     else
     {
       System.out.println("computed incorrectly");
     }

This will print:

.. code:: text

  computed correctly

Next, we will check satisfiability of the same formula,
only this time over integer variables ``a`` and ``b``.
For this, we first reset the assertions added to the solver.

.. code-block:: java

     solver.resetAssertions();

Next, we assert the same assertions as above, but with integers.
This time, we inline the construction of terms
to the assertion command.

.. code-block:: java

     solver.assertFormula(solver.mkTerm(Kind.LT, solver.mkInteger(0), a));
     solver.assertFormula(solver.mkTerm(Kind.LT, solver.mkInteger(0), b));
     solver.assertFormula(
     solver.mkTerm(Kind.LT, solver.mkTerm(Kind.PLUS, a, b), solver.mkInteger(1)));
     solver.assertFormula(solver.mkTerm(Kind.LEQ, a, b));

Now, we check whether the revised assertion is satisfiable.

.. code-block:: java

     Result r2 = solver.checkSat();

     // This time the formula is unsatisfiable
     System.out.println("expected: unsat");
     System.out.println("result: " + r2);

This time the asserted formula is unsatisfiable:

.. code:: text

  expected: unsat
  result: unsat

We can query the solver for an unsatisfiable core, that is, a subset
of the assertions that is already unsatisfiable.

.. code-block:: java

     List<Term> unsatCore = Arrays.asList(solver.getUnsatCore());
     System.out.println("unsat core size: " + unsatCore.size());
     System.out.println("unsat core: ");
     for (Term t : unsatCore)
     {
       System.out.println(t);
     }

This will print:

.. code:: text

  unsat core size: 3
  unsat core:
  (< 0 a)
  (< 0 b)
  (< (+ a b) 1)

Example
-------

| The SMT-LIB input for this example can be found at `examples/api/smtlib/quickstart.smt2 <https://github.com/cvc5/cvc5/blob/master/examples/api/smtlib/quickstart.smt2>`_.
| The source code for this example can be found at `examples/api/java/QuickStart.java <https://github.com/cvc5/cvc5/blob/master/examples/api/java/QuickStart.java>`_.

.. api-examples::
    <examples>/api/cpp/quickstart.cpp
    <examples>/api/java/QuickStart.java
    <examples>/api/python/quickstart.py
    <examples>/api/smtlib/quickstart.smt2
