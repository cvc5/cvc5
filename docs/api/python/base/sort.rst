Sort
================

The :py:obj:`Sort <cvc5.Sort>` class represents the sort of a
:py:obj:`Term <cvc5.Term>`.
Its kind is represented as enum class :py:obj:`cvc5.SortKind`.

A :py:obj:`Sort <cvc5.Sort>` can be hashed (using
:py:obj:`std.hash\<cvc5.Sort>`) and represented as a string
(using :py:func:`cvc5.Sort.__str__()`).

Class :py:obj:`cvc5.Sort` only provides the default constructor
to create a null Sort. Class :py:obj:`TermManager <cvc5.TermManager>`
provides factory functions for all other sorts, e.g.,
:py:func:`cvc5.TermManager.getBooleanSort()` for the Boolean sort and
:py:func:`cvc5.TermManager.mkBitVectorSort()` for bit-vector
sorts.

Sorts are defined as standardized in the SMT-LIB standard for standardized
theories. Additionally, we introduce the following sorts for non-standardized
theories:

- *Bag* (:doc:`Theory of Bags <../../../theories/bags>`)

  - Created with :py:func:`cvc5.TermManager.mkBagSort()`

- *Set* (:doc:`Theory of Sets and Relations <../../../theories/sets-and-relations>`)

  - Created with :py:func:`cvc5.TermManager.mkSetSort()`

- *Relation* (:doc:`Theory of Sets and Relations <../../../theories/sets-and-relations>`)

  - Created with :py:func:`cvc5.TermManager.mkSetSort()` as a set of tuple
    sorts

- *Table*

  - Created with :py:func:`cvc5.TermManager.mkBagSort()` as a bag of tuple
    sorts

----

.. autoclass:: cvc5.Sort
    :members:
    :undoc-members:
