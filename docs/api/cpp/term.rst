Term
====

The :cpp:class:`Term <cvc5::Term>` class represents arbitrary expressions that
are Boolean or from some of the supported theories. The list of all supported
types (or kinds) is given by the :cpp:enum:`Kind <cvc5::Kind>` enum.
The :cpp:class:`Term <cvc5::Term>` class provides methods for general
inspection (e.g., comparison, retrieve the kind and sort, access sub-terms),
but also methods to retrieving constant values for the supported theories
(i.e., :code:`is<Type>Value()` and :code:`get<Type>Value()`, which returns the
constant values in the best type standard C++ offers).

Additionally, a :cpp:class:`Term <cvc5::Term>` can be hashed (using
:cpp:class:`std::hash\<cvc5::Term>`) and given to output streams, including
terms within standard containers like :code:`std::map`, :code:`std::set`, or
:code:`std::vector`.

The :cpp:class:`Term <cvc5::Term>` only offers the default constructor to
create a null term. Instead, the :cpp:class:`Solver <cvc5::Solver>` class
provides factory functions for all other terms, e.g.,
:cpp:func:`Solver::mkTerm() <cvc5::Solver::mkTerm()>` for generic terms and
:code:`Solver::mk<Type>()` for constant values of a given type.

.. doxygenclass:: cvc5::Term
    :project: cvc5
    :members:
    :undoc-members:

.. doxygenstruct:: std::hash< cvc5::Term >
    :project: std
    :members:
    :undoc-members:
