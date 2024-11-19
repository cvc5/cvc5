Cvc5TermManager
===============

This struct represents a cvc5 term manager instance.

:cpp:type:`Terms <Cvc5Term>`, :cpp:type:`Sorts <Cvc5Sort>` and
:cpp:type:`Ops <Cvc5Op>` are not tied to a :cpp:type:`Cvc5`
but associated with a :cpp:type:`Cvc5TermManager` instance, which can be
shared between solver instances (and thus allows sharing of terms and sorts
between solver instances).

Term kinds are defined via enum :doc:`Cvc5Kind <../enums/cvc5kind>`, and sort
kinds via enum :doc:`Cvc5SortKind <../enums/cvc5sortkind>`.

Solver options are configured via :cpp:func:`cvc5_set_option()`
and queried via :cpp:func:`cvc5_get_option()`
(for more information on configuration options, see :doc:`../../../options`).
Information about a specific option can be retrieved via
:cpp:func:`cvc5_get_option_info()`
(see :doc:`Cvc5OptionInfo <../structs/cvc5optioninfo>`).

.. container:: hide-toctree

  .. toctree::

----

.. doxygentypedef:: Cvc5TermManager
    :project: cvc5_c

----

.. doxygengroup:: c_cvc5termmanager
    :project: cvc5_c
    :content-only:

-------------

Sort Creation
--------------

.. doxygengroup:: c_sort_creation
    :project: cvc5_c
    :content-only:

-------------

Operator Creation
-----------------

.. doxygengroup:: c_op_creation
    :project: cvc5_c
    :content-only:

-------------

Term Creation
-------------

.. doxygengroup:: c_term_creation
    :project: cvc5_c
    :content-only:

-------------

Datatype Declaration Creation
-----------------------------

.. doxygengroup:: c_dt_decl_creation
    :project: cvc5_c
    :content-only:

-------------

Datatype Constructor Declaration Creation
-----------------------------------------

.. doxygengroup:: c_dt_cons_decl_creation
    :project: cvc5_c
    :content-only:
