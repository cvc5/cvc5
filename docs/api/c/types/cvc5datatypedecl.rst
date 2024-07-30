Cvc5DatatypeDecl
================

This struct encapsulates a datatype declaration. A :cpp:type:`Cvc5DatatypeDecl`
is constructed via :cpp:func:`cvc5_mk_dt_decl()`.
This is not a :doc:`datatype <cvc5datatype>` itself, but the representation of
the specification for creating a datatype :cpp:type:`sort <Cvc5Sort>` via
:cpp:func:`cvc5_mk_dt_sort()` and :cpp:func:`cvc5_mk_dt_sorts()`.

.. container:: hide-toctree

  .. toctree::

----

.. doxygentypedef:: Cvc5DatatypeDecl
    :project: cvc5_c

----

.. doxygengroup:: c_cvc5dtdecl
    :project: cvc5_c
    :content-only:
