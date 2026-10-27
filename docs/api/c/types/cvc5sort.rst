Cvc5Sort
========

The :cpp:type:`Cvc5Sort` struct represents the sort of a :cpp:type:`Cvc5Term`.
The kind of a sort is represented as enum :cpp:enum:`Cvc5SortKind`.

A :cpp:type:`Cvc5Sort` can be hashed (using :cpp:func:`cvc5_sort_hash()`)
represented as a string (via :cpp:func:`cvc5_sort_to_string()`).

:cpp:type:`Cvc5Sort` instances are created via factory functions associated
with a :cpp:type:`Cvc5TermManager` instance, e.g.,
:cpp:func:`cvc5_get_boolean_sort()` for the Boolean sort and
:cpp:func:`cvc5_mk_bv_sort()` for bit-vector sorts.

Sorts are defined as standardized in the SMT-LIB standard for standardized
theories. Additionally, we introduce the following sorts for non-standardized
theories:

- *Bag* (:doc:`Theory of Bags <../../../theories/bags>`)

  - Created with :cpp:func:`cvc5_mk_bag_sort()`

- *Set* (:doc:`Theory of Sets and Relations <../../../theories/sets-and-relations>`)

  - Created with :cpp:func:`cvc5_mk_set_sort()`

- *Relation* (:doc:`Theory of Sets and Relations <../../../theories/sets-and-relations>`)

  - Created with :cpp:func:`cvc5_mk_set_sort()` as a set of tuple sorts

- *Table*

  - Created with :cpp:func:`cvc5_mk_bag_sort()` as a bag of tuple sorts

.. container:: hide-toctree

  .. toctree::

----

.. doxygentypedef:: Cvc5Sort
    :project: cvc5_c

----

.. doxygengroup:: c_cvc5sort
    :project: cvc5_c
    :content-only:
