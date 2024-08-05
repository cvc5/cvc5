TermManager
===========

This class represents a cvc5 term manager instance.

:cpp:class:`Terms <cvc5::Term>`, :cpp:class:`Sorts <cvc5::Sort>` and
:cpp:class:`Ops <cvc5::Op>` are not tied to a :cpp:class:`cvc5::Solver`
but associated with a :cpp:class:`cvc5::TermManager` instance, which can be
shared between solver instances (and thus allows sharing of terms and sorts
between solver instances).
Term kinds are defined via enum class :doc:`cvc5::Kind <../enums/kind>`, and
sort kinds via enum class :doc:`cvc5::SortKind <../enums/sortkind>`.

----

.. doxygenclass:: cvc5::TermManager
    :project: cvc5
    :members:
    :undoc-members:

