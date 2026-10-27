Cvc5Op
======

The :cpp:type:`Cvc5Op` struct represents a cvc5 operator, instantiated with
the parameters it requires (if any).

A :cpp:type:`Cvc5Term` of operator kind that does not require additional
parameters, e.g., :cpp:enumerator:`CVC5_KIND_ADD`, is usually constructed via
:cpp:func:`Cvc5Term cvc5_mk_term(Cvc5TermManager* tm, Cvc5Kind kind, size_t size, const Cvc5Term args[])`.
Alternatively, any :cpp:type:`Cvc5Term` can be constructed via first
instantiating a corresponding :cpp:type:`Cvc5Op`, even if the operator does
not require additional parameters.
Terms with operators that require additional parameters, e.g.,
:cpp:enumerator:`CVC5_KIND_BITVECTOR_EXTRACT`, must be created via
:cpp:func:`cvc5_mk_op()` (or :cpp:func:`cvc5_mk_op_from_str()`) and
:cpp:func:`cvc5_mk_term_from_op()`.

.. container:: hide-toctree

  .. toctree::

----

.. doxygentypedef:: Cvc5Op
    :project: cvc5_c

----

.. doxygengroup:: c_cvc5op
    :project: cvc5_c
    :content-only:
