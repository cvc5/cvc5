Sort
====

The :cpp:class:`Sort <cvc5::api::Sort>` class represents the sort of a
:cpp:class:`Term <cvc5::api::Term>`.

A :cpp:class:`Sort <cvc5::api::Sort>` can be hashed (using
:cpp:class:`std::hash\<cvc5::api::Sort>`) and serialized to an output stream
(using :cpp:func:`cvc5::api::operator<<()`).

Class :cpp:class:`Sort <cvc5::api::Sort>` offers the default constructor
only to create a null Sort. Instead, the :cpp:class:`Solver <cvc5::api::Solver>`
class provides factory functions for all other sorts, e.g.,
:cpp:func:`cvc5::api::Solver::getBooleanSort()` for Sort Bool and
:cpp:func:`cvc5::api::Solver::mkBitVectorSort()` for bit-vector
sorts.

Sorts are defined as standardized in the SMT-LIB standard for standardized
theories. Additionally, we introduce the following sorts for non-standardized
theories:

- *Bag* (Multiset)

  - Created with :cpp:func:`cvc5::api::Solver::mkBagSort()`

- *Set* (:ref:`Theory of Sets and Relations <theory_reference_sets>`)

  - Created with :cpp:func:`cvc5::api::Solver::mkSetSort()`

- *Relation* (:ref:`Theory of Sets and Relations <theory_reference_sets>`)

  - Created with :cpp:func:`cvc5::api::Solver::mkSetSort()` as a set of tuple
    sorts

- *Table*

  - Created with :cpp:func:`cvc5::api::Solver::mkBagSort()` as a bag of tuple
    sorts

.. doxygenclass:: cvc5::api::Sort
    :project: cvc5
    :members:
    :undoc-members:

.. doxygenfunction:: cvc5::api::operator<<(std::ostream& out, const Sort& s)

.. doxygenstruct:: std::hash< cvc5::api::Sort >
    :project: std
    :members:
    :undoc-members:

