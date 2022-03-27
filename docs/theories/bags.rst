Theory Reference: Bags
====================================

Finite Bags
-----------

cvc5 supports the theory of finite bags using the following sorts, constants,
functions and predicates.

For the C++ API examples in the table below, we assume that we have created
a `cvc5::api::Solver solver` object.

+----------------------+----------------------------------------------+-------------------------------------------------------------------------+
|                      | SMTLIB language                              | C++ API                                                                 |
+----------------------+----------------------------------------------+-------------------------------------------------------------------------+
| Logic String         | ``(set-logic ALL)``                          | ``solver.setLogic("ALL");``                                             |
+----------------------+----------------------------------------------+-------------------------------------------------------------------------+
| Sort                 | ``(Bag <Sort>)``                             | ``solver.mkBagSort(cvc5::api::Sort elementSort);``                      |
+----------------------+----------------------------------------------+-------------------------------------------------------------------------+
| Constants            | ``(declare-const X (Bag Int)``               | ``Sort s = solver.mkBagSort(solver.getIntegerSort());``                 |
|                      |                                              |                                                                         |
|                      |                                              | ``Term X = solver.mkConst(s, "X");``                                    |
+----------------------+----------------------------------------------+-------------------------------------------------------------------------+
| Union disjoint       | ``(bag.union_disjoint X Y)``                 | ``Term Y = solver.mkConst(s, "Y");``                                    |
|                      |                                              |                                                                         |
|                      |                                              | ``Term t = solver.mkTerm(Kind::BAG_UNION_DISJOINT, X, Y);``             |
+----------------------+----------------------------------------------+-------------------------------------------------------------------------+
| Union max            | ``(bag.union_max X Y)``                      | ``Term Y = solver.mkConst(s, "Y");``                                    |
|                      |                                              |                                                                         |
|                      |                                              | ``Term t = solver.mkTerm(Kind::BAG_UNION_MAX, X, Y);``                  |
+----------------------+----------------------------------------------+-------------------------------------------------------------------------+
| Intersection min     | ``(bag.inter_min X Y)``                      | ``Term t = solver.mkTerm(Kind::BAG_INTER_MIN, X, Y);``                  |
+----------------------+----------------------------------------------+-------------------------------------------------------------------------+
| Difference subtract  | ``(bag.difference_subtract X Y)``            | ``Term t = solver.mkTerm(Kind::BAG_DIFFERENCE_SUBTRACT, X, Y);``        |
+----------------------+----------------------------------------------+-------------------------------------------------------------------------+
| Membership           | ``(bag.member x X)``                         | ``Term x = solver.mkConst(solver.getIntegerSort(), "x");``              |
|                      |                                              |                                                                         |
|                      |                                              | ``Term t = solver.mkTerm(Kind::BAG_MEMBER, x, X);``                     |
+----------------------+----------------------------------------------+-------------------------------------------------------------------------+
| Subbag               | ``(bag.subbag X Y)``                         | ``Term t = solver.mkTerm(Kind::BAG_SUBBAG, X, Y);``                     |
+----------------------+----------------------------------------------+-------------------------------------------------------------------------+
| Emptybag             | ``(as bag.empty (Bag Int)``                  | ``Term t = solver.mkEmptyBag(s);``                                      |
+----------------------+----------------------------------------------+-------------------------------------------------------------------------+
| Make bag             | ``(bag "a" 3)``                              | ``Term t = solver.mkTerm(Kind::BAG_MAKE,                                |
|                      |                                              |            solver.mkString("a"), solver.mkInteger(1));``                                      |
+----------------------+----------------------------------------------+-------------------------------------------------------------------------+
| Cardinality          | ``(bag.card X)``                             | ``Term t = solver.mkTerm(Kind::BAG_CARD, X);``                          |
+----------------------+----------------------------------------------+-------------------------------------------------------------------------+

Semantics
^^^^^^^^^

The semantics of most of the above operators (e.g., ``bag.union``,
``bag.inter``, difference) are straightforward.
The semantics for the universe set and complement are more subtle and explained
in the following.

The universe set ``(as bag.universe (Set T))`` is *not* interpreted as the set
containing all elements of sort ``T``.
Instead it may be interpreted as any set such that all sets of sort ``(Set T)``
are interpreted as subsets of it.
In other words, it is the union of the interpretations of all (finite) sets in
our input.

For example:

.. code:: smtlib

  (declare-fun x () (Set Int))
  (declare-fun y () (Set Int))
  (declare-fun z () (Set Int))
  (assert (bag.member 0 x))
  (assert (bag.member 1 y))
  (assert (= z (as bag.universe (Set Int))))
  (check-sat)

Here, a possible model is:

.. code:: smtlib

  (define-fun x () (bag.singleton 0))
  (define-fun y () (bag.singleton 1))
  (define-fun z () (bag.union (bag.singleton 1) (bag.singleton 0)))

Notice that the universe set in this example is interpreted the same as ``z``,
and is such that all sets in this example (``x``, ``y``, and ``z``) are subsets
of it.

The set complement operator for ``(Set T)`` is interpreted relative to the
interpretation of the universe set for ``(Set T)``, and not relative to the set
of all elements of sort ``T``.
That is, for all sets ``X`` of sort ``(Set T)``, the complement operator is
such that ``(= (bag.complement X) (bag.minus (as bag.universe (Set T)) X))``
holds in all models.

The motivation for these semantics is to ensure that the universe set for sort
``T`` and applications of set complement can always be interpreted as a finite
set in (quantifier-free) inputs, even if the cardinality of ``T`` is infinite. 
Above, notice that we were able to find a model for the universe set of sort 
``(Set Int)`` that contained two elements only.

.. note::
  In the presence of quantifiers, cvc5's implementation of the above theory
  allows infinite sets.
  In particular, the following formula is SAT (even though cvc5 is not able to
  say this):

  .. code:: smtlib

    (set-logic ALL)
    (declare-fun x () (Set Int))
    (assert (forall ((z Int) (bag.member (* 2 z) x)))
    (check-sat)

  The reason for that is that making this formula (and similar ones) `unsat` is
  counter-intuitive when quantifiers are present.


Below is a more extensive example on how to use finite sets:

.. api-examples::
    <examples>/api/cpp/sets.cpp
    <examples>/api/java/Sets.java
    <examples>/api/python/sets.py
    <examples>/api/smtlib/sets.smt2

