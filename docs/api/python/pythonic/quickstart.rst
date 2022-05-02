Quickstart Guide
================

First, we create two constants ``x`` and ``y`` of sort ``Real``,
and two constants ``a`` and ``b`` of sort ``Integer``.
Notice that these are *symbolic* constants, but not actual values.

.. literalinclude:: ../../../../examples/api/python/pythonic/quickstart.py
     :language: python
     :lines: 6-7

We define the following constraints regarding ``x`` and ``y``:

.. math::

  (0 < x) \wedge (0 < y) \wedge (x + y < 1) \wedge (x \leq y)

We check whether there is a solution to these constraints:

.. literalinclude:: ../../../../examples/api/python/pythonic/quickstart.py
     :language: python
     :lines: 15

In this case, there is, so we get output:

.. code:: text

  [x = 1/6, y = 1/6]

We can also get an explicit model (assignment) for the constraints.

.. literalinclude:: ../../../../examples/api/python/pythonic/quickstart.py
     :language: python
     :lines: 19-22

With the model, we can evaluate variables and terms:

.. literalinclude:: ../../../../examples/api/python/pythonic/quickstart.py
     :language: python
     :lines: 24-26

This will print:

.. code:: text

  x: 1/6
  y: 1/6
  x - y: 0


We can also get these values in other forms:

.. literalinclude:: ../../../../examples/api/python/pythonic/quickstart.py
     :language: python
     :lines: 29-32


Next, we assert the same assertions as above, but with integers.
This time, there is no solution, so "no solution" is printed.

.. literalinclude:: ../../../../examples/api/python/pythonic/quickstart.py
     :language: python
     :lines: 36


Example
-------

.. api-examples::
    <examples>/api/python/quickstart.py
    <examples>/api/cpp/quickstart.cpp
    <examples>/api/java/QuickStart.java
    <examples>/api/python/pythonic/quickstart.py
    <examples>/api/smtlib/quickstart.smt2
