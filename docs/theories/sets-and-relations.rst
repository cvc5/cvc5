.. _theory_reference_sets:

Theory Reference: Sets and Relations
====================================

Finite Sets
-----------

cvc5 supports the theory of finite sets using the following sorts, constants,
functions and predicates.  More details can be found in :cite:`BansalBRT17`.

For the C++ API examples in the table below, we assume that we have created
a `cvc5::Solver solver` object.

+----------------------+----------------------------------------------+---------------------------------------------------------------------------+
|                      | SMTLIB language                              | C++ API                                                                   |
+----------------------+----------------------------------------------+---------------------------------------------------------------------------+
| Logic String         | append `FS` for finite sets                  | append `FS` for finite sets                                               |
|                      |                                              |                                                                           |
|                      | ``(set-logic QF_UFLIAFS)``                   | ``solver.setLogic("QF_UFLIAFS");``                                        |
+----------------------+----------------------------------------------+---------------------------------------------------------------------------+
| Sort                 | ``(Set <Sort>)``                             | ``solver.mkSetSort(cvc5::Sort elementSort);``                             |
+----------------------+----------------------------------------------+---------------------------------------------------------------------------+
| Constants            | ``(declare-const X (Set Int)``               | ``Sort s = solver.mkSetSort(solver.getIntegerSort());``                   |
|                      |                                              |                                                                           |
|                      |                                              | ``Term X = solver.mkConst(s, "X");``                                      |
+----------------------+----------------------------------------------+---------------------------------------------------------------------------+
| Union                | ``(set.union X Y)``                          | ``Term Y = solver.mkConst(s, "Y");``                                      |
|                      |                                              |                                                                           |
|                      |                                              | ``Term t = solver.mkTerm(Kind::SET_UNION, {X, Y});``                      |
+----------------------+----------------------------------------------+---------------------------------------------------------------------------+
| Intersection         | ``(set.inter X Y)``                          | ``Term t = solver.mkTerm(Kind::SET_INTER, {X, Y});``                      |
+----------------------+----------------------------------------------+---------------------------------------------------------------------------+
| Minus                | ``(set.minus X Y)``                          | ``Term t = solver.mkTerm(Kind::SET_MINUS, {X, Y});``                      |
+----------------------+----------------------------------------------+---------------------------------------------------------------------------+
| Membership           | ``(set.member x X)``                         | ``Term x = solver.mkConst(solver.getIntegerSort(), "x");``                |
|                      |                                              |                                                                           |
|                      |                                              | ``Term t = solver.mkTerm(Kind::SET_MEMBER, {x, X});``                     |
+----------------------+----------------------------------------------+---------------------------------------------------------------------------+
| Subset               | ``(set.subset X Y)``                         | ``Term t = solver.mkTerm(Kind::SET_SUBSET, {X, Y});``                     |
+----------------------+----------------------------------------------+---------------------------------------------------------------------------+
| Emptyset             | ``(as set.empty (Set Int)``                  | ``Term t = solver.mkEmptySet(s);``                                        |
+----------------------+----------------------------------------------+---------------------------------------------------------------------------+
| Singleton Set        | ``(set.singleton 1)``                        | ``Term t = solver.mkTerm(Kind::SET_SINGLETON, {solver.mkInteger(1)});``   |
+----------------------+----------------------------------------------+---------------------------------------------------------------------------+
| Cardinality          | ``(set.card X)``                             | ``Term t = solver.mkTerm(Kind::SET_CARD, {X});``                          |
+----------------------+----------------------------------------------+---------------------------------------------------------------------------+
| Insert / Finite Sets | ``(set.insert 1 2 3 (set.singleton 4))``     | ``Term one = solver.mkInteger(1);``                                       |
|                      |                                              |                                                                           |
|                      |                                              | ``Term two = solver.mkInteger(2);``                                       |
|                      |                                              |                                                                           |
|                      |                                              | ``Term three = solver.mkInteger(3);``                                     |
|                      |                                              |                                                                           |
|                      |                                              | ``Term sgl = solver.mkTerm(Kind::SET_SINGLETON, {solver.mkInteger(4)});`` |
|                      |                                              |                                                                           |
|                      |                                              | ``Term t = solver.mkTerm(Kind::SET_INSERT, {one, two, three, sgl});``     |
+----------------------+----------------------------------------------+---------------------------------------------------------------------------+
| Complement           | ``(set.complement X)``                       | ``Term t = solver.mkTerm(Kind::SET_COMPLEMENT, {X});``                    |
+----------------------+----------------------------------------------+---------------------------------------------------------------------------+
| Universe Set         | ``(as set.universe (Set Int))``              | ``Term t = solver.mkUniverseSet(s);``                                     |
+----------------------+----------------------------------------------+---------------------------------------------------------------------------+


Semantics
^^^^^^^^^

The semantics of most of the above operators (e.g., ``set.union``,
``set.inter``, difference) are straightforward.
The semantics for the universe set and complement are more subtle and explained
in the following.

The universe set ``(as set.universe (Set T))`` is *not* interpreted as the set
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
  (assert (set.member 0 x))
  (assert (set.member 1 y))
  (assert (= z (as set.universe (Set Int))))
  (check-sat)

Here, a possible model is:

.. code:: smtlib

  (define-fun x () (set.singleton 0))
  (define-fun y () (set.singleton 1))
  (define-fun z () (set.union (set.singleton 1) (set.singleton 0)))

Notice that the universe set in this example is interpreted the same as ``z``,
and is such that all sets in this example (``x``, ``y``, and ``z``) are subsets
of it.

The set complement operator for ``(Set T)`` is interpreted relative to the
interpretation of the universe set for ``(Set T)``, and not relative to the set
of all elements of sort ``T``.
That is, for all sets ``X`` of sort ``(Set T)``, the complement operator is
such that ``(= (set.complement X) (set.minus (as set.universe (Set T)) X))``
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
    (assert (forall ((z Int) (set.member (* 2 z) x)))
    (check-sat)

  The reason for that is that making this formula (and similar ones) `unsat` is
  counter-intuitive when quantifiers are present.


Below is a more extensive example on how to use finite sets:

.. api-examples::
    <examples>/api/cpp/sets.cpp
    <examples>/api/java/Sets.java
    <examples>/api/python/sets.py
    <examples>/api/smtlib/sets.smt2


Finite Relations
----------------

cvc5 also supports the theory of finite relations, using the following sorts,
constants, functions and predicates.
More details can be found in :cite:`MengRTB17`.

+----------------------+----------------------------------------------+------------------------------------------------------------------------------------+
|                      | SMTLIB language                              | C++ API                                                                            |
+----------------------+----------------------------------------------+------------------------------------------------------------------------------------+
| Logic String         | ``(set-logic QF_ALL)``                       | ``solver.setLogic("QF_ALL");``                                                     |
+----------------------+----------------------------------------------+------------------------------------------------------------------------------------+
| Tuple Sort           | ``(Tuple <Sort_1>, ..., <Sort_n>)``          | ``std::vector<cvc5::Sort> sorts = { ... };``                                       |
|                      |                                              |                                                                                    |
|                      |                                              | ``Sort s = solver.mkTupleSort(sorts);``                                            |
+----------------------+----------------------------------------------+------------------------------------------------------------------------------------+
|                      | ``(declare-const t (Tuple Int Int))``        | ``Sort s_int = solver.getIntegerSort();``                                          |
|                      |                                              |                                                                                    |
|                      |                                              | ``Sort s = solver.mkTupleSort({s_int, s_int});``                                   |
|                      |                                              |                                                                                    |
|                      |                                              | ``Term t = solver.mkConst(s, "t");``                                               |
+----------------------+----------------------------------------------+------------------------------------------------------------------------------------+
| Tuple Constructor    | ``(tuple <Term_1>, ..., <Term_n>)``          | ``Term t = solver.mkTuple({<Sort_1>, ..., <Sort_n>}, {Term_1>, ..., <Term_n>});``  |
+----------------------+----------------------------------------------+------------------------------------------------------------------------------------+
| Tuple Selector       | ``((_ tuple_select i) t)``                   | ``Sort s = solver.mkTupleSort(sorts);``                                            |
|                      |                                              |                                                                                    |
|                      |                                              | ``Datatype dt = s.getDatatype();``                                                 |
|                      |                                              |                                                                                    |
|                      |                                              | ``Term c = dt[0].getSelector();``                                                  |
|                      |                                              |                                                                                    |
|                      |                                              | ``Term t = solver.mkTerm(Kind::APPLY_SELECTOR, {s, t});``                          |
+----------------------+----------------------------------------------+------------------------------------------------------------------------------------+
| Relation Sort        | ``(Relation <Sort_1>, ..., <Sort_n>)``       | ``Sort s = solver.mkSetSort(cvc5::Sort tupleSort);``                               |
|                      |                                              |                                                                                    |
|                      | which is a syntax sugar for                  |                                                                                    |
|                      |                                              |                                                                                    |
|                      | ``(Set (Tuple <Sort_1>, ..., <Sort_n>))``    |                                                                                    |
+----------------------+----------------------------------------------+------------------------------------------------------------------------------------+
| Constants            | ``(declare-const X (Set (Tuple Int Int)``    | ``Sort s = solver.mkSetSort(solver.mkTupleSort({s_int, s_int});``                  |
|                      |                                              |                                                                                    |
|                      |                                              | ``Term X = solver.mkConst(s, "X");``                                               |
+----------------------+----------------------------------------------+------------------------------------------------------------------------------------+
| Transpose            | ``(rel.transpose X)``                        | ``Term t = solver.mkTerm(Kind::RELATION_TRANSPOSE, X);``                           |
+----------------------+----------------------------------------------+------------------------------------------------------------------------------------+
| Transitive Closure   | ``(rel.tclosure X)``                         | ``Term t = solver.mkTerm(Kind::RELATION_TCLOSURE, X);``                            |
+----------------------+----------------------------------------------+------------------------------------------------------------------------------------+
| Join                 | ``(rel.join X Y)``                           | ``Term t = solver.mkTerm(Kind::RELATION_JOIN, X, Y);``                             |
+----------------------+----------------------------------------------+------------------------------------------------------------------------------------+
| Product              | ``(rel.product X Y)``                        | ``Term t = solver.mkTerm(Kind::RELATION_PRODUCT, X, Y);``                          |
+----------------------+----------------------------------------------+------------------------------------------------------------------------------------+

Example:

.. api-examples::
    <examples>/api/cpp/relations.cpp
    <examples>/api/java/Relations.java
    <examples>/api/python/relations.py
    <examples>/api/smtlib/relations.smt2
