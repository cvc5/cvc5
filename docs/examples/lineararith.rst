Theory of Linear Arithmetic
===========================

This example asserts three constraints over an integer variable :code:`x` and a real variable :code:`y`.
Firstly, it checks that these constraints entail an upper bound on the difference :code:`y - x <= 2/3`.
Secondly, it checks that this bound is tight by asserting :code:`y - x = 2/3` and checking for satisfiability.
The two checks are separated by using :code:`push` and :code:`pop`.

.. api-examples::
    <examples>/api/cpp/linear_arith.cpp
    <examples>/api/java/LinearArith.java
    <examples>/api/python/pythonic/linear_arith.py
    <examples>/api/python/linear_arith.py
    <examples>/api/smtlib/linear_arith.smt2
