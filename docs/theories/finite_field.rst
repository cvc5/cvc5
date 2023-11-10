Theory Reference: Finite Fields
===============================

.. note::
  Currently, cvc5 only supports finite fields of prime order p.
   Such a field is isomorphic to the integers modulo p.

Semantics
^^^^^^^^^

First, for integer :math:`x` and positive integer :math:`y`, define :math:`(x \bmod y)` as the unique integer :math:`r` such that :math:`y = qx + r` (where :math:`q` is an integer) and :math:`0 \le r < q`.
NB: This is the remainder when so-called "floor division" is performed.

We interpret field sorts as prime fields and field terms as integers. In the following, let:

* ``N`` be an integer numeral and :math:`N` be its integer
* ``p`` be a prime numeral and :math:`p` be its prime
* ``F`` be an SMT field sort (of order :math:`p`)
* ``x`` and ``y`` be SMT field terms (of the same sort ``F``) with interpretations :math:`x` and :math:`y`

+-----------------------+--------------------------------------------+----------------------------------------------+
| SMT construct         | Semantics                                  | Notes                                        |
+=======================+============================================+==============================================+
| ``(_ FiniteField p)`` | the field of order :math:`p`               | represented as the integers modulo :math:`p` |
+-----------------------+--------------------------------------------+----------------------------------------------+
| ``(as ffN F)``        | the integer :math:`(N \bmod p)`            |                                              |
+-----------------------+--------------------------------------------+----------------------------------------------+
| ``(ff.add x y)``      | the integer :math:`((x + y) \bmod p)`      | NB: ``ff.add`` is an n-ary operator          |
+-----------------------+--------------------------------------------+----------------------------------------------+
| ``(ff.mul x y)``      | the integer :math:`((x \times y) \bmod p)` | NB: ``ff.mul`` is an n-ary operator          |
+-----------------------+--------------------------------------------+----------------------------------------------+
| ``(= x y)``           | the Boolean :math:`x = y`                  |                                              |
+-----------------------+--------------------------------------------+----------------------------------------------+


Syntax
^^^^^^

For the C++ API examples in the table below, we assume that we have created
a :cpp:class:`Solver <cvc5::Solver>` object ``solver``.

+----------------------+----------------------------------------------+--------------------------------------------------------------------+
|                      | SMT-LIB language                             | C++ API                                                            |
+======================+==============================================+====================================================================+
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

