Theory Reference: Datatypes
===========================

cvc5 implements some extensions to the support for datatypes in SMT-LIB 2.

Logic
-----

To enable cvc5's decision procedure for datatypes, include ``DT`` in the logic:

.. code:: smtlib

  (set-logic QF_UFDT)

Alternatively, use the ``ALL`` logic:

.. code:: smtlib

  (set-logic ALL)

Syntax
------

cvc5 supports the following syntax for declaring mutually recursive blocks of
datatypes in ``*.smt2`` input files in the smt lib 2.6 format:

.. code:: smtlib

  (declare-datatypes ((D1 n1) ... (Dk nk))
   (((C1 (S1 T1) ... (Si Ti)) ... (Cj ... ))
    ...
    ((...) ... (...)))

where ``D1 ... Dk`` are datatype types, ``C1 ... Cj`` are the constructors for
datatype ``D1``,
``S1 ... Si`` are the selectors (or "destructors") of constructor ``C1``, and
each ``T1 ... Ti`` is a previously declared type or one of ``D1 ... Dk``.
The symbols ``U1 ... Un`` are type parameters (fresh symbols).
The numbers ``n1 ... nk`` denote the number of type
parameters for the datatype, where ``0`` is used for non-parametric datatypes.

In addition to declaring symbols for constructors and selectors, the above
command also adds tester (or "discriminator") indexed symbols of the form
``(_ is C)`` for each constructor ``C``, which are unary predicates which
evaluate to true iff their argument has top-symbol ``C``.

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
  (assert (= ((_ tuple_select 0) t) 3))
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
a `cvc5::api::Solver solver` object.

+--------------------+----------------------------------------+---------------------------------------------------------------------------------------------------------------------------------+
|                    | SMTLIB language                        | C++ API                                                                                                                         |
+--------------------+----------------------------------------+---------------------------------------------------------------------------------------------------------------------------------+
| Logic String       | ``(set-logic QF_DT)``                  | ``solver.setLogic("QF_DT");``                                                                                                   |
+--------------------+----------------------------------------+---------------------------------------------------------------------------------------------------------------------------------+
| Tuple Sort         | ``(Tuple <Sort_1>, ..., <Sort_n>)``    | ``std::vector<cvc5::api::Sort> sorts = { ... };``                                                                               |
|                    |                                        |                                                                                                                                 |
|                    |                                        | ``Sort s = solver.mkTupleSort(sorts);``                                                                                         |
+--------------------+----------------------------------------+---------------------------------------------------------------------------------------------------------------------------------+
|                    | ``(declare-const t (Tuple Int Int))``  | ``Sort s_int = solver.getIntegerSort();``                                                                                       |
|                    |                                        |                                                                                                                                 |
|                    |                                        | ``Sort s = solver.mkTupleSort({s_int, s_int});``                                                                                |
|                    |                                        |                                                                                                                                 |
|                    |                                        | ``Term t = solver.mkConst(s, "t");``                                                                                            |
+--------------------+----------------------------------------+---------------------------------------------------------------------------------------------------------------------------------+
| Tuple Constructor  | ``(mkTuple <Term_1>, ..., <Term_n>)``  | ``Sort s = solver.mkTupleSort(sorts);``                                                                                         |
|                    |                                        |                                                                                                                                 |
|                    |                                        | ``Datatype dt = s.getDatatype();``                                                                                              |
|                    |                                        |                                                                                                                                 |
|                    |                                        | ``Term c = dt[0].getConstructor();``                                                                                            |
|                    |                                        |                                                                                                                                 |
|                    |                                        | ``Term t = solver.mkTerm(Kind::APPLY_CONSTRUCTOR, {c, <Term_1>, ..., <Term_n>});``                                              |
+--------------------+----------------------------------------+---------------------------------------------------------------------------------------------------------------------------------+
| Tuple Selector     | ``((_ tuple_select i) t)``             | ``Sort s = solver.mkTupleSort(sorts);``                                                                                         |
|                    |                                        |                                                                                                                                 |
|                    |                                        | ``Datatype dt = s.getDatatype();``                                                                                              |
|                    |                                        |                                                                                                                                 |
|                    |                                        | ``Term c = dt[0].getSelector();``                                                                                               |
|                    |                                        |                                                                                                                                 |
|                    |                                        | ``Term t = solver.mkTerm(Kind::APPLY_SELECTOR, {s, t});``                                                                       |
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
|                    |                                        | ``Term c = dt[0].getConstructor();``                                                                                            |
|                    |                                        |                                                                                                                                 |
|                    |                                        | ``Term t = solver.mkTerm(Kind::APPLY_CONSTRUCTOR, {c, <Term_1>, ..., <Term_n>});``                                              |
+--------------------+----------------------------------------+---------------------------------------------------------------------------------------------------------------------------------+
| Record Selector    | n/a                                    | ``Sort s = mkRecordSort(fields);``                                                                                              |
|                    |                                        |                                                                                                                                 |
|                    |                                        | ``Datatype dt = s.getDatatype();``                                                                                              |
|                    |                                        |                                                                                                                                 |
|                    |                                        | ``Term c = dt[0].getSelector();``                                                                                               |
|                    |                                        |                                                                                                                                 |
|                    |                                        | ``Term t = solver.mkTerm(Kind::APPLY_CONSTRUCTOR, {s, <Term_1>, ..., <Term_n>});``                                              |
+--------------------+----------------------------------------+---------------------------------------------------------------------------------------------------------------------------------+
