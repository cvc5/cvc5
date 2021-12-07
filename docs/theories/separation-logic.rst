Theory Reference: Separation Logic
==================================

cvc5 supports a syntax for separation logic as an extension of the SMT-LIB 2
language.

Signature
---------

Given a (decidable) base theory :math:`T`, cvc5 implements a decision procedure
for quantifier-free :math:`SL(T)_{Loc,Data}` formulas :cite:`ReynoldsISK16`,
where :math:`Loc` and :math:`Data` are any sort belonging to :math:`T`.

A :math:`SL(T)_{Loc,Data}` formula is one from the following grammar:

.. code::

  F : L | (emp t u) | (pto t u) | (sep F1 ... Fn) | (wand F1 F2) | ~F1 | F1 op ... op Fn

where ``op`` is any classical Boolean connective, ``t`` and ``u`` are terms
built from symbols in the signature of :math:`T` of sort :math:`Loc` and
:math:`Data` respectively, and :math:`L` is a :math:`T`-literal.

The operator ``emp`` denotes the empty heap constraint, the operator ``pto``
denotes the points-to predicate, the operator ``sep`` denotes separation start
and is variadic, and the operator ``wand`` denote magic wand.

Semantics
---------

A satisfiability relation :math:`I,h \models_{SL} \varphi` is defined for
:math:`SL(T)_{Loc,Data}` formulas :math:`\varphi`,
where :math:`I` is an interpretation, and :math:`h` is a heap.

The semantics of separation logic operators are as follows:

+-------------------------------------------------------------+------+-------------------------------------------------------------------------------------+
| :math:`I,h \models_{SL} L`                                  | Iff  | :math:`I \models L`, if :math:`L` is a :math:`T`-literal                            |
+-------------------------------------------------------------+------+-------------------------------------------------------------------------------------+
| :math:`I,h \models_{SL}` (emp :math:`t \ u`)                | Iff  | :math:`h = \emptyset`                                                               |
+-------------------------------------------------------------+------+-------------------------------------------------------------------------------------+
| :math:`I,h \models_{SL}` (pto :math:`t \ u`)                | Iff  | :math:`h = \{(t^I,u^I)\} \text{ and } t^I\not=nil^I`                                |
+-------------------------------------------------------------+------+-------------------------------------------------------------------------------------+
| :math:`I,h \models_{SL}` (sep :math:`\phi_1 \ldots \phi_n)` | Iff  | there exist heaps :math:`h_1,\ldots,h_n` s.t. :math:`h=h_1\uplus \ldots \uplus h_n` |
|                                                             |      |                                                                                     |
|                                                             |      | and :math:`I,h_i \models_{SL} \phi_i, i = 1,\ldots,n`                               |
+-------------------------------------------------------------+------+-------------------------------------------------------------------------------------+
| :math:`I,h \models_{SL}` (wand :math:`\phi_1 \ \phi_2`)     | Iff  | for all heaps :math:`h'` if :math:`h'\#h` and :math:`I,h' \models_{SL} \phi_1`      |
|                                                             |      |                                                                                     |
|                                                             |      | then :math:`I,h'\uplus h \models_{SL} \phi_2`                                       |
+-------------------------------------------------------------+------+-------------------------------------------------------------------------------------+

where :math:`h_1 \uplus \ldots \uplus h_n` denotes the disjoint union of heaps
:math:`h_1, \ldots, h_n` and :math:`h'\#h` denotes that heaps :math:`h'` and
:math:`h` are disjoint, and :math:`nil` is a distinguished variable of sort
:math:`Loc`.
All classical Boolean connectives are interpreted as expected.

.. note::
  The arguments of ``emp`` are used to denote the sort of the heap and have no
  meaning otherwise.

Syntax
------

Separation logic in cvc5 requires the ``QF_ALL`` logic.

The syntax for the operators of separation logic is summarized in the following
table.
For the C++ API examples in this table, we assume that we have created
a :cpp:class:`cvc5::api::Solver` object.

+----------------------+----------------------------------------------+--------------------------------------------------------------------+
|                      | SMTLIB language                              | C++ API                                                            |
+----------------------+----------------------------------------------+--------------------------------------------------------------------+
| Logic String         | ``(set-logic QF_ALL)``                       | ``solver.setLogic("QF_ALL");``                                     |
+----------------------+----------------------------------------------+--------------------------------------------------------------------+
| Empty Heap           | ``(_ emp <Sort_1> <Sort_2>)``                | ``solver.mkTerm(Kind::SEP_EMP, x, y);``                            |
|                      |                                              |                                                                    |
|                      |                                              | where ``x`` and ``y`` are of sort ``<Sort_1>`` and ``<Sort_2>``    |
+----------------------+----------------------------------------------+--------------------------------------------------------------------+
| Points-To            | ``(pto x y)``                                | ``solver.mkTerm(Kind::SEP_PTO, x, y);``                            |
+----------------------+----------------------------------------------+--------------------------------------------------------------------+
| Separation Star      | ``(sep c1 .. cn)``                           | ``solver.mkTerm(Kind::SEP_STAR, {c1, ..., cn});``                  |
+----------------------+----------------------------------------------+--------------------------------------------------------------------+
| Magic Wand           | ``(wand c1 c1)``                             | ``solver.mkTerm(Kind::SEP_WAND, c1, c2);``                         |
+----------------------+----------------------------------------------+--------------------------------------------------------------------+
| Nil Element          | ``(as nil <Sort>)``                          | ``solver.mkSepNil(cvc5::api::Sort sort);``                         |
+----------------------+----------------------------------------------+--------------------------------------------------------------------+


Examples
--------

The following input on heaps ``Int -> Int`` is unsatisfiable:

.. code:: smtlib

  (set-logic QF_ALL)
  (set-info :status unsat)
  (declare-const x Int)
  (declare-const a Int)
  (declare-const b Int)
  (assert (and (pto x a) (pto x b)))
  (assert (not (= a b)))
  (check-sat)


The following input on heaps ``U -> Int`` is satisfiable. Notice that the
formula ``(not (emp x 0))`` is satisfied by heaps ``U -> Int`` (the sorts of
``x`` and ``0`` respectively) whose domain is non-empty.

.. code:: smtlib

  (set-logic QF_ALL)
  (set-info :status sat)
  (declare-sort U 0)
  (declare-const x U)
  (declare-const a Int)
  (assert (and (not (_ emp U Int)) (pto x a)))
  (check-sat)

The following input on heaps ``Int -> Node`` is satisfiable, where ``Node``
denotes a user-defined inductive :doc:`datatypes`.

.. code:: smtlib

  (set-logic QF_ALL)
  (set-info :status sat)
  (declare-const x Int)
  (declare-const y Int)
  (declare-const z Int)
  (declare-datatype Node ((node (data Int) (left Int) (right Int))))
  (assert (pto x (node 0 y z)))
  (check-sat)

.. note::

  Given a separation logic input, the sorts :math:`Loc` and :math:`Data` are
  inferred by cvc5, and must be consistent across all predicates occurring in
  an input.
  cvc5 does not accept an input such as:

  .. code:: smtlib

    (set-logic QF_ALL)
    (declare-sort U 0)
    (declare-const x U)
    (assert (and (pto x 0) (pto 1 2)))
    (check-sat)

  since the sorts of the first arguments of the points-to predicates do not
  agree.
