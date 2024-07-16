TermManager
===========

This class represents a cvc5 term manager instance.

:py:obj:`Terms <cvc5.Term>`, :py:obj:`Sorts <cvc5.Sort>` and
:py:obj:`Ops <cvc5.Op>` are not tied to a :py:obj:`cvc5.Solver`
but associated with a :py:obj:`cvc5.TermManager` instance, which can be
shared between solver instances (and thus allows sharing of terms and sorts
between solver instances).
Term kinds are defined via enum class :doc:`cvc5.Kind <kind>`, and
sort kinds via enum class :doc:`cvc5.SortKind <sortkind>`.

----

.. autoclass:: cvc5.TermManager
    :members:
    :undoc-members:

