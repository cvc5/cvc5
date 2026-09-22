Cvc5Term
========

The :cpp:type:`Cvc5Term` struct represents an arbitrary expression
of any of the supported sorts. The list of all supported kinds of terms is
given by the :cpp:enum:`Cvc5Kind` enum.
The :cpp:type:`Cvc5Term` struct provides functions for general inspection
(e.g., comparison, retrieving the kind and sort, accessing sub-terms),
but also functions for retrieving constant values for the supported theories
(i.e., :code:`cvc5_term_is_*_value()` and :code:`cvc5_term_get_*_value()`,
which returns the constant values in the best type standard C++ offers).

Additionally, a :cpp:type:`Cvc5Term` can be hashed (using
:cpp:func:`cvc5_term_hash()`) and represented as string
(via :cpp:func:`cvc5_term_to_string()`).

:cpp:type:`Cvc5Term` instances are created via factory functions associated
with a :cpp:type:`Cvc5TermManager` instance, e.g.,
:cpp:func:`cvc5_mk_term()` for generic terms of a specific kind and
:code:`cvc5_mk_<type>()` for constants, variables and values of a given type.

.. container:: hide-toctree

  .. toctree::

----

.. doxygentypedef:: Cvc5Term
    :project: cvc5_c

----

.. doxygengroup:: c_cvc5term
    :project: cvc5_c
    :content-only:
