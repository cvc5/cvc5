Theory Reference: Finite Fields
===============================

.. note::
  current, cvc5 only supports finite fields of prime order p.
   Such a field is isomorphic to the integers modulo p.

Semantics
^^^^^^^^^

.. code-block::

  * First, for integer x and positive integer y, define x % y as the unique
    integer r such that y = q*x + r (where q is an integer) and 0 <= r < q.
    NB: This is the remainder when so-called "floor division" is performed.

  * (_ FiniteField p)

    ⟦(_ FiniteField p)⟧ = the finite field or order p: the integers modulo p.

  * (as ffN F)

    ⟦(as ffN F)⟧ = the integer (N % p), where p is the order of F

  * (ff.add x y)

    ⟦(ff.add x y)⟧ = the integer ((⟦x⟧ + ⟦y⟧) % p), where x, y are in the same
                     field of order p

    NB: the ff.add operator is n-ary.

  * (ff.mul x y)

    ⟦(ff.mul x y)⟧ = the integer ((⟦x⟧ * ⟦y⟧) % p), where x, y are in the same
                     field of order p

    NB: the ff.mul operator is n-ary.

  * (= x y)

    ⟦(= x y)⟧ = the Boolean ⟦x⟧ = ⟦y⟧ are equal, when x, y are in the same field.


Syntax
^^^^^^

For the C++ API examples in the table below, we assume that we have created
a ``cvc5::api::Solver solver`` object.

+----------------------+----------------------------------------------+--------------------------------------------------------------------+
|                      | SMT-LIB language                             | C++ API                                                            |
+----------------------+----------------------------------------------+--------------------------------------------------------------------+
| Logic String         | use `FF` for finite fields                   | use `FF` for finite fields                                         |
|                      |                                              |                                                                    |
|                      | ``(set-logic QF_FF)``                        | ``solver.setLogic("QF_FF");``                                      |
+----------------------+----------------------------------------------+--------------------------------------------------------------------+
| Sort                 | ``(_ FiniteField <Prime Order>)``            | ``solver.mkFiniteFieldSort(<Prime Order As String>);``             |
+----------------------+----------------------------------------------+--------------------------------------------------------------------+
| Constants            | ``(declare-const X (_ FiniteField 7))``      | ``Sort s = solver.mkFiniteFieldSort("7");``                        |
|                      |                                              |                                                                    |
|                      |                                              | ``Term X = solver.mkConst(s, "X");``                               |
+----------------------+----------------------------------------------+--------------------------------------------------------------------+
| Finite Field Value   | ``(as ff3 (_ FiniteField 7))``               | ``Sort ffSort = solver.mkFiniteFieldSort("7");``                   |
|                      |                                              |                                                                    |
|                      |                                              | ``Term t = solver.mkFiniteFieldElem("3", ffSort);``                |
+----------------------+----------------------------------------------+--------------------------------------------------------------------+
| Addition             | ``(ff.add x y)``                             | ``Term t = solver.mkTerm(Kind::FINITE_FIELD_ADD, {x, y});``        |
+----------------------+----------------------------------------------+--------------------------------------------------------------------+
| Multiplication       | ``(ff.mul x y)``                             | ``Term t = solver.mkTerm(Kind::FINITE_FIELD_MULT, {x, y});``       |
+----------------------+----------------------------------------------+--------------------------------------------------------------------+
| Equality             | ``(= x y)``                                  | ``Term t = solver.mkTerm(Kind::EQUAL, {x, y});``                   |
+----------------------+----------------------------------------------+--------------------------------------------------------------------+


Examples
^^^^^^^^

.. code:: smtlib

  (set-logic QF_FF)
  (set-info :status unsat)
  (define-sort F () (_ FiniteField 3))
  (declare-const x F)
  (assert (= (ff.mul x x) (as ff-1 F)))
  (check-sat)
  ; unsat

.. code:: smtlib

  (set-logic QF_FF)
  (set-info :status sat)
  (define-sort F () (_ FiniteField 3))
  (declare-const x F)
  (assert (= (ff.mul x x) (as ff0 F)))
  (check-sat)
  ; sat: (= x (as ff0 F)) is the only model

.. code:: smtlib

  (set-logic QF_FF)
  (set-info :status unsat)
  (define-sort F () (_ FiniteField 3))
  (declare-const x F)
  (declare-const y F)
  (declare-const z F)
  (assert (= (ff.mul (ff.add x y z) (ff.add x y z)) (as ff-1 F)))
  (check-sat)
  ; unsat


References
^^^^^^^^^^

The theory of finite fields was defined in
"Satisfiability Modulo Finite Fields" :cite:`Ozdemir23`.
See the paper for more information.

