Theory Reference: Datatypes
===========================

cvc5 implements some extensions to the support for datatypes in SMT-LIB 2.

Logic
-----

To enable cvc5's decision procedure for datatypes, include ``DT`` in the logic:

.. code:: smtlib

  (set-logic QF_DT)

Alternatively, use the ``ALL`` logic:

.. code:: smtlib

  (set-logic ALL)

Syntax
------

cvc5 supports the following syntax for declaring mutually recursive blocks of
datatypes in ``*.smt2`` input files in the smt lib 2.6 format:

.. code:: smtlib

  (declare-datatypes ((D1 n1) ... (Dk nk))
   (((C1 (S11 T1) ... (S1i Ti)) ... (Cj ... ))
    ...
    ((...) ... (...)))

where ``D1 ... Dk`` are datatype types, ``C1 ... Cj`` are the constructors for
datatype ``D1``,
``S11 ... S1i`` are the selectors (or "destructors") of constructor ``C1``, and
each ``T1 ... Ti`` is a previously declared type or one of ``D1 ... Dk``.
The numbers ``n1 ... nk`` denote the number of type
parameters for the datatype, where ``0`` is used for non-parametric datatypes.

In addition to declaring symbols for constructors and selectors, the above
command also allows for tester (or "discriminator") indexed symbols of the form
``(_ is C)`` for each constructor ``C``, which are unary predicates which
evaluate to true iff their argument has top-symbol ``C``. It also allows for
updater indexed symbols of the form ``(_ update Sij)`` for each selector ``Sij``,
whose semantics are described below.

Semantics
---------

The decision procedure for inductive datatypes is described in
:cite:`BarrettST07`.

Example Declarations
--------------------

An enumeration:

.. code:: smtlib

  (declare-datatypes ((Color 0))
   (((Red) (Black))))

A List of ``Int`` with ``cons`` and ``nil`` as constructors:

.. code:: smtlib

  (declare-datatypes ((list 0))
   (((cons (head Int) (tail list)) (nil))))

A parametric List of T's:

.. code:: smtlib

  (declare-datatypes ((list 1))
   ((par (T) ((cons (head T) (tail (list T))) (nil)))))

Mutual recursion:

.. code:: smtlib

  (declare-datatypes ((list 0) (tree 0))
   (((cons (head tree) (tail list)) (nil))
    ((node (data Int) (children list)))))

A (non-recursive) record type:

.. code:: smtlib

  (declare-datatypes ((record 0))
   (((rec (fname String) (lname String) (id Int)))))


Examples
--------

.. code:: smtlib

  (declare-datatypes ((list 0))
     (((cons (head Int) (tail list)) (nil))))
   (declare-const a list)
   (declare-const b list)
   (assert (and (= (tail a) b) (not ((_ is nil) b)) (> (head b) 0)))
   (check-sat)

.. code:: smtlib

   (declare-datatypes ((record 0))
     (((rec (fname String) (lname String) (id Int)))))
   (declare-const x record)
   (assert (and (= (fname x) "John") (= (lname x) "Smith")))
   (check-sat)

Datatype Updaters
--------------------

Datatype updaters are a (non-standard) extension available in datatype logics.
The term:

.. code:: smtlib

   ((_ update Sij) t u)

is equivalent to replacing the field of ``t`` denoted by the selector ``Sij``
with the value ``u``, or ``t`` itself if that selector does not apply to the
constructor symbol of ``t``.  For example, for the list datatype, we have that:

.. code:: smtlib

   ((_ update head) (cons 4 nil) 7) = (cons 7 nil)
   ((_ update tail) (cons 4 nil) (cons 5 nil)) = (cons 4 (cons 5 nil))
   ((_ update head) nil 5) = nil

Note that datatype updaters can be seen as syntax sugar for an if-then-else
term that checks whether the constructor of ``t`` is the same as the one
associated with the given selector.

Parametric Datatypes
--------------------

Instances of parametric datatypes must have their arguments instantiated with
concrete types. For instance, in the example:

.. code:: smtlib

  (declare-datatypes ((list 1)) ((par (T) (cons (head T) (tail (list T))) (nil))))

To declare a list of ``Int``, use the command:

.. code:: smtlib

  (declare-const f (list Int))

Use of constructors that are ambiguously typed must be cast to a concrete type,
for instance all occurrences of ``nil`` for the above datatype must be cast with
the syntax:

.. code:: smtlib

  (as nil (list Int))

Tuples
------

Tuples are a particular instance of an inductive datatype. cvc5 supports
special syntax for tuples as an extension of the SMT-LIB version 2 format.
For example:

.. code:: smtlib

  (declare-const t (Tuple Int Int))
  (assert (= ((_ tuple.select 0) t) 3))
  (assert (not (= t (tuple 3 4))))


Codatatypes
-----------

cvc5 also supports co-inductive datatypes, as described in
:cite:`ReynoldsB15`.

The syntax for declaring mutually recursive coinductive datatype blocks is
identical to inductive datatypes, except that ``declare-datatypes`` is replaced
by ``declare-codatatypes``. For example, the following declares the type denote
streams of ``Int``:

.. code:: smtlib

  (declare-codatatypes ((stream 0))
   (((cons (head Int) (tail stream)))))


Syntax/API
----------

For the C++ API examples in the table below, we assume that we have created
a `cvc5::Solver solver` object.

+--------------------+----------------------------------------+---------------------------------------------------------------------------------------------------------------------------------+
|                    | SMTLIB language                        | C++ API                                                                                                                         |
+--------------------+----------------------------------------+---------------------------------------------------------------------------------------------------------------------------------+
| Logic String       | ``(set-logic QF_DT)``                  | ``solver.setLogic("QF_DT");``                                                                                                   |
+--------------------+----------------------------------------+---------------------------------------------------------------------------------------------------------------------------------+
| Datatype Sort      | ``(declare-datatype ...)``             | ``Sort s = solver.mkDatatypeSort(...);``                                                                                        |
+--------------------+----------------------------------------+---------------------------------------------------------------------------------------------------------------------------------+
| Datatype Sorts     | ``(declare-datatypes ...)``            | ``std::vector<Sort> s = solver.mkDatatypeSorts(...);``                                                                          |
+--------------------+----------------------------------------+---------------------------------------------------------------------------------------------------------------------------------+
| Constructor        | ``(Ci <Term_1>, ..., <Term_n>)``       | ``Sort s = solver.mkDatatypeSort(...);``                                                                                        |
|                    |                                        |                                                                                                                                 |
|                    |                                        | ``Datatype dt = s.getDatatype();``                                                                                              |
|                    |                                        |                                                                                                                                 |
|                    |                                        | ``Term ci = dt[i].getTerm();``                                                                                                  |
|                    |                                        |                                                                                                                                 |
|                    |                                        | ``Term r = solver.mkTerm(Kind::APPLY_CONSTRUCTOR, {ci, <Term_1>, ..., <Term_n>});``                                             |
+--------------------+----------------------------------------+---------------------------------------------------------------------------------------------------------------------------------+
| Selector           | ``(Sij t)``                            | ``Sort s = solver.mkDatatypeSort(...);``                                                                                        |
|                    |                                        |                                                                                                                                 |
|                    |                                        | ``Datatype dt = s.getDatatype();``                                                                                              |
|                    |                                        |                                                                                                                                 |
|                    |                                        | ``Term sij = dt[i].getSelector(j).getTerm();``                                                                                  |
|                    |                                        |                                                                                                                                 |
|                    |                                        | ``Term r = solver.mkTerm(Kind::APPLY_SELECTOR, {sij, t});``                                                                     |
+--------------------+----------------------------------------+---------------------------------------------------------------------------------------------------------------------------------+
| Updater            | ``((_ update Sij) t u)``               | ``Sort s = solver.mkDatatypeSort(...);``                                                                                        |
|                    |                                        |                                                                                                                                 |
|                    |                                        | ``Datatype dt = s.getDatatype();``                                                                                              |
|                    |                                        |                                                                                                                                 |
|                    |                                        | ``Term upd = dt[i].getSelector(j).getUpdaterTerm();``                                                                           |
|                    |                                        |                                                                                                                                 |
|                    |                                        | ``Term r = solver.mkTerm(Kind::APPLY_UPDATER, {upd, t, u});``                                                                   |
+--------------------+----------------------------------------+---------------------------------------------------------------------------------------------------------------------------------+
| Tester             | ``((_ is Ci) t)``                      | ``Sort s = solver.mkDatatypeSort(...);``                                                                                        |
|                    |                                        |                                                                                                                                 |
|                    |                                        | ``Datatype dt = s.getDatatype();``                                                                                              |
|                    |                                        |                                                                                                                                 |
|                    |                                        | ``Term upd = dt[i].getTesterTerm();``                                                                                           |
|                    |                                        |                                                                                                                                 |
|                    |                                        | ``Term r = solver.mkTerm(Kind::APPLY_TESTER, {upd, t, u});``                                                                    |
+--------------------+----------------------------------------+---------------------------------------------------------------------------------------------------------------------------------+
| Tuple Sort         | ``(Tuple <Sort_1>, ..., <Sort_n>)``    | ``std::vector<cvc5::Sort> sorts = { ... };``                                                                                    |
|                    |                                        |                                                                                                                                 |
|                    |                                        | ``Sort s = solver.mkTupleSort(sorts);``                                                                                         |
+--------------------+----------------------------------------+---------------------------------------------------------------------------------------------------------------------------------+
|                    | ``(declare-const t (Tuple Int Int))``  | ``Sort s_int = solver.getIntegerSort();``                                                                                       |
|                    |                                        |                                                                                                                                 |
|                    |                                        | ``Sort s = solver.mkTupleSort({s_int, s_int});``                                                                                |
|                    |                                        |                                                                                                                                 |
|                    |                                        | ``Term t = solver.mkConst(s, "t");``                                                                                            |
+--------------------+----------------------------------------+---------------------------------------------------------------------------------------------------------------------------------+
| Tuple Constructor  | ``(tuple  <Term_1>, ..., <Term_n>)``   | ``Sort s = solver.mkTupleSort(sorts);``                                                                                         |
|                    |                                        |                                                                                                                                 |
|                    |                                        | ``Datatype dt = s.getDatatype();``                                                                                              |
|                    |                                        |                                                                                                                                 |
|                    |                                        | ``Term c = dt[0].getTerm();``                                                                                                   |
|                    |                                        |                                                                                                                                 |
|                    |                                        | ``Term r = solver.mkTerm(Kind::APPLY_CONSTRUCTOR, {c, <Term_1>, ..., <Term_n>});``                                              |
+--------------------+----------------------------------------+---------------------------------------------------------------------------------------------------------------------------------+
| Tuple Selector     | ``((_ tuple.select i) t)``             | ``Sort s = solver.mkTupleSort(sorts);``                                                                                         |
|                    |                                        |                                                                                                                                 |
|                    |                                        | ``Datatype dt = s.getDatatype();``                                                                                              |
|                    |                                        |                                                                                                                                 |
|                    |                                        | ``Term sel = dt[0].getSelector(i).getTerm();``                                                                                  |
|                    |                                        |                                                                                                                                 |
|                    |                                        | ``Term r = solver.mkTerm(Kind::APPLY_SELECTOR, {sel, t});``                                                                     |
+--------------------+----------------------------------------+---------------------------------------------------------------------------------------------------------------------------------+
| Tuple Updater      | ``((_ tuple.update i) t u)``           | ``Sort s = solver.mkTupleSort(sorts);``                                                                                         |
|                    |                                        |                                                                                                                                 |
|                    |                                        | ``Datatype dt = s.getDatatype();``                                                                                              |
|                    |                                        |                                                                                                                                 |
|                    |                                        | ``Term upd = dt[0].getSelector(i).getUpdaterTerm();``                                                                           |
|                    |                                        |                                                                                                                                 |
|                    |                                        | ``Term r = solver.mkTerm(Kind::APPLY_UPDATER, {upd, t, u});``                                                                   |
+--------------------+----------------------------------------+---------------------------------------------------------------------------------------------------------------------------------+
| Tuple Projection   | ``((_ tuple.project i1 ... in) t)``    | ``Sort s = solver.mkTupleSort(sorts);``                                                                                         |
|                    |                                        |                                                                                                                                 |
|                    |                                        | ``Datatype dt = s.getDatatype();``                                                                                              |
|                    |                                        |                                                                                                                                 |
|                    |                                        | ``Term proj = solver.mkOp(Kind::TUPLE_PROJECT, {i1, ..., in});``                                                                |
|                    |                                        |                                                                                                                                 |
|                    |                                        | ``Term r = solver.mkTerm(Kind::TUPLE_PROJECT, {proj, t});``                                                                     |
+--------------------+----------------------------------------+---------------------------------------------------------------------------------------------------------------------------------+
| Record Sort        | n/a                                    | ``Sort s = mkRecordSort(const std::vector<std::pair<std::string, Sort>>& fields);``                                             |
+--------------------+----------------------------------------+---------------------------------------------------------------------------------------------------------------------------------+
|                    | n/a                                    | ``std::vector<std::pair<std::string, Sort>> fields;``                                                                           |
|                    |                                        |                                                                                                                                 |
|                    |                                        | ``fields.push_back(std::pair<std::string, Sort>("fst", solver.getIntegerSort()));``                                             |
|                    |                                        |                                                                                                                                 |
|                    |                                        | ``fields.push_back(std::pair<std::string, Sort>("snd", solver.getIntegerSort()));``                                             |
|                    |                                        |                                                                                                                                 |
|                    |                                        | ``Sort s = mkRecordSort(fields);``                                                                                              |
+--------------------+----------------------------------------+---------------------------------------------------------------------------------------------------------------------------------+
| Record Constructor | n/a                                    | ``Sort s = mkRecordSort(fields);``                                                                                              |
|                    |                                        |                                                                                                                                 |
|                    |                                        | ``Datatype dt = s.getDatatype();``                                                                                              |
|                    |                                        |                                                                                                                                 |
|                    |                                        | ``Term c = dt[0].getTerm();``                                                                                                   |
|                    |                                        |                                                                                                                                 |
|                    |                                        | ``Term r = solver.mkTerm(Kind::APPLY_CONSTRUCTOR, {c, <Term_1>, ..., <Term_n>});``                                              |
+--------------------+----------------------------------------+---------------------------------------------------------------------------------------------------------------------------------+
| Record Selector    | n/a                                    | ``Sort s = mkRecordSort(fields);``                                                                                              |
|                    |                                        |                                                                                                                                 |
|                    |                                        | ``Datatype dt = s.getDatatype();``                                                                                              |
|                    |                                        |                                                                                                                                 |
|                    |                                        | ``Term sel = dt[0].getSelector(name).getSelectorTerm();``                                                                       |
|                    |                                        |                                                                                                                                 |
|                    |                                        | ``Term r = solver.mkTerm(Kind::APPLY_SELECTOR, {sel, t});``                                                                     |
+--------------------+----------------------------------------+---------------------------------------------------------------------------------------------------------------------------------+
| Record Updater     | n/a                                    | ``Sort s = solver.mkRecordSort(sorts);``                                                                                        |
|                    |                                        |                                                                                                                                 |
|                    |                                        | ``Datatype dt = s.getDatatype();``                                                                                              |
|                    |                                        |                                                                                                                                 |
|                    |                                        | ``Term upd = dt[0].getSelector(name).getUpdaterTerm();``                                                                        |
|                    |                                        |                                                                                                                                 |
|                    |                                        | ``Term r = solver.mkTerm(Kind::APPLY_UPDATER, {upd, t, u});``                                                                   |
+--------------------+----------------------------------------+---------------------------------------------------------------------------------------------------------------------------------+
