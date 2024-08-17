Cvc5
====

This struct represents a cvc5 solver instance.

:cpp:type:`Terms <Cvc5Term>`, :cpp:type:`sorts <Cvc5Sort>` and
:cpp:type:`operators <Cvc5Op>` are not tied to a :cpp:type:`Cvc5` instance
but associated with a :cpp:type:`Cvc5TermManager` instance, which can be
shared between solver instances.

Solver options are configured via :cpp:func:`cvc5_set_option()`
and queried via :cpp:func:`cvc5_get_option()`
(for more information on configuration options, see :doc:`../../../options`).
Information about a specific option can be retrieved via
:cpp:func:`cvc5_get_option_info()` (see :doc:`../structs/cvc5optioninfo`).


.. container:: hide-toctree

  .. toctree::

----

.. doxygentypedef:: Cvc5
    :project: cvc5_c

----

.. doxygengroup:: c_cvc5
    :project: cvc5_c
    :content-only:
