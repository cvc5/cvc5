C API
=====

The C API of cvc5 is based on its :doc:`C++ API <../cpp/cpp>` and is
**feature complete**, within the limits of the C language.
The :doc:`quickstart guide <quickstart>` gives a short introduction of how
to use cvc5 via its C API.
For most applications, the :cpp:type:`Cvc5` solver struct is the main
entry point to cvc5.

One of the key differences is the way **how memory is managed**. While users of
the C++ API can rely on memory being efficiently managed automatically, on the
C level, management to maintain a low overhead needs **more manual
intervention**.

The C API offers **two modes** of memory management:

1. Let cvc5 handle memory management without manual intervention. All memory
   allocated by the C API via a term manager (:cpp:type:`Cvc5TermManager`) or
   solver (:cpp:type:`Cvc5`) instance will only be released when these
   instances are deleted via :cpp:func:`cvc5_delete()` and
   :cpp:func:`cvc5_term_manager_delete()`. For example:

.. code:: c

   Cvc5TermManager* tm = cvc5_term_manager_new();
   Cvc5* cvc5 = cvc5_new(tm);
   Cvc5Term a = cvc5_mk_const(tm, cvc5_get_integer_sort(tm), "a");
   Cvc5Term two = cvc5_mk_integer_int64(tm, 2);
   Cvc5Term args1[2] = {a, two};
   cvc5_assert_formula(cvc5, cvc5_mk_term(tm, CVC5_KIND_EQUAL, 2, args1));
   Cvc5Term b = cvc5_mk_const(tm, cvc5_get_integer_sort(tm), "b");
   Cvc5Term args2[2] = {b, two};
   cvc5_assert_formula(cvc5, cvc5_mk_term(tm, CVC5_KIND_DISTINCT, 2, args2));
   cvc5_check_sat(cvc5);
   cvc5_delete(cvc5);
   cvc5_term_manager_delete(tm);


2. Introduce a more fine-grained, user-level memory management for objects
   created via a term manager or solver via the corresponding ``cvc5_*_copy()``
   and ``cvc5_*_release()`` functions. The copy functions increment the
   reference counter of an object, the release functions decrement the
   reference counter and free its allocated memory when the counter reaches 0.
   For example:

.. code:: c

   Cvc5TermManager* tm = cvc5_term_manager_new();
   Cvc5* cvc5 = cvc5_new(tm);
   Cvc5Term a = cvc5_mk_const(tm, cvc5_get_integer_sort(tm), "a");
   Cvc5Term two = cvc5_mk_integer_int64(tm, 2);
   Cvc5Term args1[2] = {a, two};
   cvc5_assert_formula(cvc5, cvc5_mk_term(tm, CVC5_KIND_EQUAL, 2, args1));
   // we can release 'a' here, not needed anymore
   cvc5_term_release(a);
   Cvc5Term b = cvc5_mk_const(tm, cvc5_get_integer_sort(tm), "b");
   Cvc5Term args2[2] = {b, two};
   cvc5_assert_formula(cvc5, cvc5_mk_term(tm, CVC5_KIND_DISTINCT, 2, args2));
   cvc5_check_sat(cvc5);
   cvc5_delete(cvc5);
   cvc5_term_manager_delete(tm);


.. container:: hide-toctree

  .. toctree::

   quickstart
   types/cvc5
   types/cvc5command
   types/cvc5datatype
   types/cvc5datatypedecl
   types/cvc5datatypeconstructor
   types/cvc5datatypeconstructordecl
   types/cvc5datatypeselector
   types/cvc5grammar
   types/cvc5inputparser
   types/cvc5op
   types/cvc5proof
   types/cvc5result
   types/cvc5sort
   types/cvc5statistics
   types/cvc5symbolmanager
   types/cvc5synthresult
   types/cvc5term
   types/cvc5termmanager
   structs/cvc5optioninfo.rst
   structs/cvc5plugin
   enums/cvc5kind
   enums/cvc5sortkind
   enums/cvc5roundingmode
   enums/cvc5unknownexplanation
   enums/modes


---------

Types
-----

The following types are defined via typedefs but used as black boxes, their
internals are hidden.

- typedef struct :doc:`types/cvc5`
- typedef struct :doc:`types/cvc5command`
- typedef struct :doc:`types/cvc5datatype`
- typedef struct :doc:`types/cvc5datatypedecl`
- typedef struct :doc:`types/cvc5datatypeconstructor`
- typedef struct :doc:`types/cvc5datatypeconstructordecl`
- typedef struct :doc:`types/cvc5datatypeselector`
- typedef struct :doc:`types/cvc5grammar`
- typedef struct :doc:`types/cvc5inputparser`
- typedef struct :doc:`types/cvc5op`
- typedef struct :doc:`types/cvc5proof`
- typedef struct :doc:`types/cvc5result`
- typedef struct :doc:`types/cvc5sort`
- typedef struct :cpp:type:`Cvc5Stat`
- typedef struct :doc:`types/cvc5statistics`
- typedef struct :doc:`types/cvc5symbolmanager`
- typedef struct :doc:`types/cvc5synthresult`
- typedef struct :doc:`types/cvc5term`
- typedef struct :doc:`types/cvc5termmanager`

Structs
-------

The following structs are fully exposed via the API.

- struct :doc:`structs/cvc5optioninfo`
- struct :doc:`structs/cvc5plugin`

Enums
------

- enum :doc:`enums/cvc5kind`
- enum :doc:`enums/cvc5sortkind`
- enum :cpp:enum:`Cvc5OptionInfoKind`
- enum :doc:`enums/cvc5roundingmode`
- enum :doc:`enums/cvc5unknownexplanation`

- enums for :doc:`configuration modes <enums/modes>`

  - enum :cpp:enum:`Cvc5BlockModelsMode`
  - enum :cpp:enum:`Cvc5LearnedLitType`
  - enum :cpp:enum:`Cvc5FindSynthTarget`
  - enum :cpp:enum:`Cvc5OptionCategory`
  - enum :cpp:enum:`Cvc5ProofComponent`
  - enum :cpp:enum:`Cvc5ProofFormat`

- enums classes for :doc:`proof rules <enums/cvc5proofrule>`

  - enum :cpp:enum:`Cvc5ProofRule`
  - enum :cpp:enum:`Cvc5ProofRewriteRule`
