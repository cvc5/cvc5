Theory Reference: Transcendentals
=================================

cvc5 supports transcendental functions that naturally extend the nonlinear real arithmetic theories ``NRA`` and ``NIRA``.
The theory consists of the constant :math:`\pi` and function symbols for most common transcendental functions like, e.g., ``sin``, ``cos`` and ``tan``.

Logic
-----

To enable cvc5's decision procedure for transcendentals, append ``T`` to the arithmetic logic that is being used:

.. code:: smtlib

  (set-logic QF_NRAT)

Alternatively, use the ``ALL`` logic:

.. code:: smtlib

  (set-logic ALL)

Syntax
------

cvc5 internally defines a constant ``real.pi`` of sort ``Real`` and the following unary function symbols from ``Real`` to ``Real``:

* the square root function ``sqrt``
* the exponential function ``exp``
* the sine function ``sin``
* the cosine function ``cos``
* the tangent function ``tan``
* the cosecant function ``csc``
* the secant function ``sec``
* the cotangent function ``cot``
* the arcsine function ``arcsin``
* the arccosine function ``arccos``
* the arctangent function ``arctan``
* the arccosecant function ``arccsc``
* the arcsecant function ``arcsec``
* the arccotangent function ``arccot``


Semantics
---------

Both the constant ``real.pi`` and all function symbols are defined on real numbers and are thus not subject to limited precision. That being said, cvc5 internally uses inexact techniques based on incremental linearization.
While ``real.pi`` is specified using a rational enclosing interval that is automatically refined on demand, the function symbols are approximated using tangent planes and secant lines using the techniques described in :cite:`DBLP:journals/tocl/CimattiGIRS18`.

Examples
--------

.. api-examples::
    <examples>/api/cpp/transcendentals.cpp
    <examples>/api/java/Transcendentals.java
    <examples>/api/python/transcendentals.py
    <examples>/api/smtlib/transcendentals.smt2