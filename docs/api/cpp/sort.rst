Sort
====

The :cpp:class:`Sort <cvc5::Sort>` class represents the sort of a
:cpp:class:`Term <cvc5::Term>`.

A :cpp:class:`Sort <cvc5::Sort>` can be hashed (using
:cpp:class:`std::hash\<cvc5::Sort>`) and serialized to an output stream
(using :cpp:func:`cvc5::operator<<()`).

Class :cpp:class:`Sort <cvc5::Sort>` offers the default constructor
only to create a null Sort. Instead, the :cpp:class:`Solver <cvc5::Solver>`
class provides factory functions for all other sorts, e.g.,
:cpp:func:`cvc5::Solver::getBooleanSort()` for Sort Bool and
:cpp:func:`cvc5::Solver::mkBitVectorSort()` for bit-vector
sorts.

Sorts are defined as standardized in the SMT-LIB standard for standardized
theories. Additionally, we introduce the following sorts for non-standardized
theories:

- *Bag* (Multiset)

  - Created with :cpp:func:`cvc5::Solver::mkBagSort()`

- *Set* (:ref:`Theory of Sets and Relations <theory_reference_sets>`)

  - Created with :cpp:func:`cvc5::Solver::mkSetSort()`

- *Relation* (:ref:`Theory of Sets and Relations <theory_reference_sets>`)

  - Created with :cpp:func:`cvc5::Solver::mkSetSort()` as a set of tuple
    sorts

- *Table*

  - Created with :cpp:func:`cvc5::Solver::mkBagSort()` as a bag of tuple
    sorts

.. doxygenclass:: cvc5::Sort
    :project: cvc5
    :members:
    :undoc-members:

.. doxygenfunction:: cvc5::operator<<(std::ostream& out, const Sort& s)

.. doxygenstruct:: std::hash< cvc5::Sort >
    :project: std
    :members:
    :undoc-members:

