Term
================

The :py:obj:`Term <cvc5.Term>` class represents an arbitrary expression
of any of the supported sorts. The list of all supported kinds of terms is
given by the :py:obj:`Kind <cvc5.Kind>` enum.
The :py:obj:`Term <cvc5.Term>` class provides functions for general
inspection (e.g., comparison, retrieving the kind and sort, accessing
sub-terms),
but also functions for retrieving constant values for the supported theories
(i.e., :code:`is<Type>Value()` and :code:`get<Type>Value()`, which returns the
constant values in the best type Python offers).

The :py:obj:`TermManager <cvc5.TermManager>` class provides factory functions
to create terms, e.g.,
:py:func:`TermManager.mkTerm() <cvc5.TermManager.mkTerm()>` for generic terms
and :code:`TermManager.mk<Type>()` for constants, variables and values of a
given type.

----

.. autoclass:: cvc5.Term
    :members:
    :special-members: __getitem__, __iter__
    :undoc-members:
