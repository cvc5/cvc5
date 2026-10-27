Cvc5DatatypeSelector
====================

This struct represents a datatype selector. A :cpp:type:`Cvc5DatatypeSelector`
is specified via :cpp:func:`cvc5_dt_cons_decl_add_selector()`,
:cpp:func:`cvc5_dt_cons_decl_add_selector_self()`
and :cpp:func:`cvc5_dt_cons_decl_add_selector_unresolved()`,
when constructing a datatype sort and can be retrieved from a
:cpp:type:`Cvc5DatatypeConstructor` via
:cpp:func:`cvc5_dt_cons_get_selector()`.

.. container:: hide-toctree

  .. toctree::

----

.. doxygentypedef:: Cvc5DatatypeSelector
    :project: cvc5_c

----

.. doxygengroup:: c_cvc5dtsel
    :project: cvc5_c
    :content-only:
