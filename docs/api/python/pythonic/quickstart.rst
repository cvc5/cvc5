Quickstart Guide
================

First, we create two constants ``x`` and ``y`` of sort ``Real``,
and two constants ``a`` and ``b`` of sort ``Integer``.
Notice that these are *symbolic* constants, but not actual values.

.. literalinclude:: ../../../../examples/api/python/pythonic/quickstart.py
   :language: python
   :dedent: 4
   :start-after: docs-pythonic-quickstart-1 start
   :end-before: docs-pythonic-quickstart-1 end

We define the following constraints regarding ``x`` and ``y``:

.. math::

  (0 < x) \wedge (0 < y) \wedge (x + y < 1) \wedge (x \leq y)

We check whether there is a solution to these constraints:

.. literalinclude:: ../../../../examples/api/python/pythonic/quickstart.py
   :language: python
   :dedent: 4
   :start-after: docs-pythonic-quickstart-2 start
   :end-before: docs-pythonic-quickstart-2 end

In this case, there is, so we get output:

.. code:: text

  [x = 1/6, y = 1/6]

We can also get an explicit model (assignment) for the constraints.

.. literalinclude:: ../../../../examples/api/python/pythonic/quickstart.py
   :language: python
   :dedent: 4
   :start-after: docs-pythonic-quickstart-3 start
   :end-before: docs-pythonic-quickstart-3 end

With the model, we can evaluate variables and terms:

.. literalinclude:: ../../../../examples/api/python/pythonic/quickstart.py
   :language: python
   :dedent: 4
   :start-after: docs-pythonic-quickstart-4 start
   :end-before: docs-pythonic-quickstart-4 end

This will print:

.. code:: text

  x: 1/6
  y: 1/6
  x - y: 0


We can also get these values in other forms:

.. literalinclude:: ../../../../examples/api/python/pythonic/quickstart.py
   :language: python
   :dedent: 4
   :start-after: docs-pythonic-quickstart-5 start
   :end-before: docs-pythonic-quickstart-5 end


Next, we assert the same assertions as above, but with integers.
This time, there is no solution, so "no solution" is printed.

.. literalinclude:: ../../../../examples/api/python/pythonic/quickstart.py
   :language: python
   :dedent: 4
   :start-after: docs-pythonic-quickstart-6 start
   :end-before: docs-pythonic-quickstart-6 end


Example
-------

.. api-examples::
    <examples>/api/python/quickstart.py
    <examples>/api/cpp/quickstart.cpp
    <examples>/api/java/QuickStart.java
    <examples>/api/python/pythonic/quickstart.py
    <examples>/api/smtlib/quickstart.smt2
