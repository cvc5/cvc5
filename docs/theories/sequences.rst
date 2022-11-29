Theory Reference: Sequences
===========================

.. note::
  cvc5 currently only supports sequences where the element sort either has an
  infinite domain, e.g., sequences of integers, or a finite domain of a fixed
  cardinality, e.g. bit-vectors.

Semantics
^^^^^^^^^

.. code-block::

  * (seq.empty (Seq S))

    ⟦seq.empty⟧ = []

  * (seq.unit S (Seq S))

    ⟦seq.unit⟧(x) = [x]

  * (seq.len (Seq S) Int)

    ⟦seq.len⟧(s) is the length of the sequence s, denoted as |s|.

  * (seq.nth ((Seq S) Int) S)

    ⟦seq.nth⟧(s, i) is the n-th element in the sequence s,
                    denoted as nth(s, i).
                    It is uninterpreted if i out of bounds, 
                    i.e. i < 0 or i >= |s|.

  * (seq.update ((Seq S) Int (Seq S)) (Seq S))

    ⟦seq.update⟧(s, i, sub) is a sequence obtained by updating the continuous
                            sub-sequence of s starting at index i by sub.
                            The updated sequence has the same length as |s|.
                            If i + |sub| > |s|,
                            the out of bounds part of sub is ignored.
                            If i out of bounds, i.e. i < 0 or i >= |s|,
                            the updated sequence remains same with s.
  
  * (seq.extract ((Seq S) Int Int) (Seq S))

    ⟦seq.extract⟧(s, i, j) is the maximal sub-sequence of s that starts at
                           index i and has length at most j,
                           in case both i and j are non-negative and i is
                           smaller than |s|.
                           Otherwise, the return value is the empty sequence.

   * (seq.++ ((Seq S) (Seq S)) (Seq S))

    ⟦seq.++⟧(s1, s2) is a sequence that is the concatenation of s1 and s2.

   * (seq.at ((Seq S) Int) (Seq S))

    ⟦seq.at⟧(s, i) is a unit sequence that contains the i-th element of s as
                   the only element, or is the empty sequence if i < 0 or i > |s|.

   * (seq.contains ((Seq S) (Seq S)) Bool)

    ⟦seq.contains⟧(s, sub) is true if sub is a continuous sub-sequence of s,
                           i.e. sub = seq.extract(s, i, j) for some i, j,
                           and false if otherwise.
  
   * (seq.indexof ((Seq S) (Seq S) Int) Int)

    ⟦seq.indexof⟧(s, sub, i) is the first position of sub at or after i in s,
                             and -1 if there is no occurrence.

   * (seq.replace ((Seq S) (Seq S) (Seq S)) (Seq S))

    ⟦seq.replace⟧(s, src, dst) is the sequence obtained by replacing the
                               first occurrence of src by dst in s.
                               It is s if there is no occurrence.

   * (seq.replace_all ((Seq S) (Seq S) (Seq S)) (Seq S))

    ⟦seq.replace_all⟧(s, src, dst) is the sequence obtained by replacing all
                                   the occurrences of src by dst in s,
                                   in the order from left to right.
                                   It is s if there is no occurrence.

   * (seq.rev (Seq S) (Seq S))

    ⟦seq.rev⟧(s) is the sequence obtained by reversing s.

   * (seq.prefixof ((Seq S) (Seq S)) Bool)

    ⟦seq.prefixof⟧(pre s) is true if pre is a prefix of s, false otherwise.

   * (seq.suffixof ((Seq S) (Seq S)) Bool)

    ⟦seq.suffixof⟧(suf s) is true if suf is a suffix of s, false otherwise.

Syntax
^^^^^^

For the C++ API examples in the table below, we assume that we have created
a ``cvc5::api::Solver solver`` object.

+----------------------+----------------------------------------------+--------------------------------------------------------------------+
|                      | SMT-LIB language                             | C++ API                                                            |
+----------------------+----------------------------------------------+--------------------------------------------------------------------+
| Logic String         | use `S` for sequences and strings            | use `S` for sequences and strings                                  |
|                      |                                              |                                                                    |
|                      | ``(set-logic QF_SLIA)``                      | ``solver.setLogic("QF_SLIA");``                                    |
+----------------------+----------------------------------------------+--------------------------------------------------------------------+
| Sort                 | ``(Seq <Sort>)``                             | ``solver.mkSequenceSort(<Sort>);``                                 |
+----------------------+----------------------------------------------+--------------------------------------------------------------------+
| Constants            | ``(declare-const X (Seq Int))``              | ``Sort s = solver.mkSequenceSort(solver.getIntegerSort());``       |
|                      |                                              |                                                                    |
|                      |                                              | ``Term X = solver.mkConst(s, "X");``                               |
+----------------------+----------------------------------------------+--------------------------------------------------------------------+
| Empty sequence       | ``(as seq.empty (Seq Int))``                 | ``Sort intSort = solver.getIntegerSort();``                        |
|                      |                                              |                                                                    |
|                      |                                              | ``Term t = solver.mkEmptySequence(intSort);``                      |
+----------------------+----------------------------------------------+--------------------------------------------------------------------+
| Unit sequence        | ``(seq.unit 1)``                             | ``Term t = solver.mkTerm(Kind::SEQ_UNIT, {solver.mkInteger(1)});`` |
+----------------------+----------------------------------------------+--------------------------------------------------------------------+
| Sequence length      | ``(seq.len X)``                              | ``Term t = solver.mkTerm(Kind::SEQ_LENGTH, {X});``                 |
+----------------------+----------------------------------------------+--------------------------------------------------------------------+
| Element access       | ``(seq.nth X i)``                            | ``Term t = solver.mkTerm(Kind::SEQ_NTH, {X, i});``                 |
+----------------------+----------------------------------------------+--------------------------------------------------------------------+
| Element update       | ``(seq.update X i Y)``                       | ``Term t = solver.mkTerm(Kind::SEQ_UPDATE, {X, i, Y});``           |
+----------------------+----------------------------------------------+--------------------------------------------------------------------+
| Extraction           | ``(seq.extract X i j)``                      | ``Term t = solver.mkTerm(Kind::SEQ_EXTRACT, {X, i, j});``          |
+----------------------+----------------------------------------------+--------------------------------------------------------------------+
| Concatenation        | ``(seq.++ X Y)``                             | ``Term t = solver.mkTerm(Kind::SEQ_CONCAT, {X, Y});``              |
+----------------------+----------------------------------------------+--------------------------------------------------------------------+
| Sub-sequence with    | ``(seq.at X i)``                             | ``Term t = solver.mkTerm(Kind::SEQ_AT, {X, i});``                  |
| single element       |                                              |                                                                    |
+----------------------+----------------------------------------------+--------------------------------------------------------------------+
| Sequence containment | ``(seq.contains X Y)``                       | ``Term t = solver.mkTerm(Kind::SEQ_CONTAINS, {X, Y});``            |
+----------------------+----------------------------------------------+--------------------------------------------------------------------+
| Sequence indexof     | ``(seq.indexof X Y i)``                      | ``Term t = solver.mkTerm(Kind::SEQ_INDEXOF, {X, Y, i});``          |
+----------------------+----------------------------------------------+--------------------------------------------------------------------+
| Sub-sequence replace | ``(seq.replace X Y Z)``                      | ``Term t = solver.mkTerm(Kind::SEQ_REPLACE, {X, Y, Z});``          |
+----------------------+----------------------------------------------+--------------------------------------------------------------------+
| Sub-sequence         | ``(seq.replace_all X Y Z)``                  | ``Term t = solver.mkTerm(Kind::SEQ_REPLACE_ALL, {X, Y, Z});``      |
| replace all          |                                              |                                                                    |
+----------------------+----------------------------------------------+--------------------------------------------------------------------+
| Sequence reverse     | ``(seq.rev X)``                              | ``Term t = solver.mkTerm(Kind::SEQ_REV, {X});``                    |
+----------------------+----------------------------------------------+--------------------------------------------------------------------+
| Sequence prefix of   | ``(seq.prefixof X Y)``                       | ``Term t = solver.mkTerm(Kind::SEQ_PREFIX, {X, Y});``              |
+----------------------+----------------------------------------------+--------------------------------------------------------------------+
| Sequence suffix of   | ``(seq.suffixof X Y)``                       | ``Term t = solver.mkTerm(Kind::SEQ_SUFFIX, {X, Y});``              |
+----------------------+----------------------------------------------+--------------------------------------------------------------------+

Examples
^^^^^^^^

.. code:: smtlib

  (set-logic QF_SLIA)
  (set-info :status unsat)
  (declare-fun x () (Seq Int))
  (declare-fun y () (Seq Int))
  (declare-fun z () (Seq Int))
  (declare-fun a () Int)
  (declare-fun b () Int)
  (assert (= y (seq.update x 0 (seq.unit a))))
  (assert (= z (seq.update x 0 (seq.unit b))))
  (assert (not (= a b)))
  (assert (= y z))
  (assert (> (seq.len y) 0))
  (check-sat)

.. code:: smtlib

  (set-logic QF_SLIA)
  (set-info :status unsat)
  (declare-fun A () (Seq Int))
  (declare-fun S () (Seq Int))
  (declare-fun i () Int)
  (assert (<= 0 i))
  (assert (< i (- (seq.len A) 1)))
  (assert (= S (seq.extract A i 1)))
  (assert (distinct (seq.nth S 0) (seq.nth A i)))
  (check-sat)

.. code:: smtlib

  (set-logic QF_SLIA)
  (set-info :status unsat)
  (declare-fun x () (Seq Int))
  (declare-fun y () (Seq Int))
  (declare-fun a () Int)
  (declare-fun b () Int)
  (assert (= (seq.++ (seq.unit a) y) (seq.update x 0 (seq.unit b))))
  (assert (not (= a b)))
  (check-sat)

