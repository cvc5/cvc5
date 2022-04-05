Quickstart Guide
================

First, we create two constants ``x`` and ``y`` of sort ``Real``,
and two constants ``a`` and ``b`` of sort ``Integer``.
Notice that these are *symbolic* constants, but not actual values.

.. literalinclude:: quickstart.py
     :language: python
     :lines: 9-10

We define the following constraints regarding ``x`` and ``y``:

.. math::

  (0 < x) \wedge (0 < y) \wedge (x + y < 1) \wedge (x \leq y)

We check whether there is a solution to these constraints:

.. literalinclude:: quickstart.py
     :language: python
     :lines: 18

In this case, there is, so we get output:

.. code:: text

  [x = 1/6, y = 1/6]

We can also get an explicit model (assignment) for the constraints.

.. literalinclude:: quickstart.py
     :language: python
     :lines: 22-25

With the model, we can evaluate variables and terms:

.. literalinclude:: quickstart.py
     :language: python
     :lines: 27-29

This will print:

.. code:: text

  x: 1/6
  y: 1/6
  x - y: 0


We can also get these values in other forms:

.. literalinclude:: quickstart.py
     :language: python
     :lines: 32-35


Next, we assert the same assertions as above, but with integers.
This time, there is no solution, so "no solution" is printed.

.. literalinclude:: quickstart.py
     :language: python
     :lines: 39


Example
-------

.. api-examples::
    <examples>/api/python/quickstart.py
    <examples>/api/cpp/quickstart.cpp
    <examples>/api/java/QuickStart.java
    <pythonicapi>/test/pgms/example_quickstart.py
    <examples>/api/smtlib/quickstart.smt2
