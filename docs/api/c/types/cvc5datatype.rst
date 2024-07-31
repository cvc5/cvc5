Cvc5Datatype
============

This struct represents a datatype. A :cpp:type:`Cvc5Datatype` is encapsulated
by a datatype :cpp:type:`sort <Cvc5Sort>` and can be retrieved from a
datatype sort via :cpp:func:`cvc5_sort_get_datatype()`.
Datatypes are specified by a :cpp:type:`Cvc5DatatypeDecl` via
:cpp:func:`cvc5_mk_dt_decl()` when constructing a datatype sort.

.. container:: hide-toctree

  .. toctree::

----

.. doxygentypedef:: Cvc5Datatype
    :project: cvc5_c

----

.. doxygengroup:: c_cvc5dt
    :project: cvc5_c
    :content-only:
