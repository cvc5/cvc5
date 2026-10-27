Term
====

The :cpp:class:`Term <cvc5::Term>` class represents an arbitrary expression
of any of the supported sorts. The list of all supported kinds of terms is
given by the :cpp:enum:`Kind <cvc5::Kind>` enum.
The :cpp:class:`Term <cvc5::Term>` class provides functions for general
inspection (e.g., comparison, retrieving the kind and sort, accessing
sub-terms),
but also functions for retrieving constant values for the supported theories
(i.e., :code:`is<Type>Value()` and :code:`get<Type>Value()`, which returns the
constant values in the best type standard C++ offers).

Additionally, a :cpp:class:`Term <cvc5::Term>` can be hashed (using
:cpp:class:`std::hash\<cvc5::Term>`) and given to output streams, including
terms within standard containers like :code:`std::map`, :code:`std::set`, or
:code:`std::vector`.

The :cpp:class:`Term <cvc5::Term>` only offers the default constructor to
create a null term. Instead, the :cpp:class:`TermManager <cvc5::TermManager>`
class provides factory functions to create terms, e.g.,
:cpp:func:`TermManager::mkTerm() <cvc5::TermManager::mkTerm()>` for generic
terms and :code:`TermManager::mk<Type>()` for constants, variables and values
of a given type.

----

- class :cpp:class:`cvc5::Term`
- :cpp:func:`std::ostream& cvc5::operator<< (std::ostream& out, const Term& t)`
- :cpp:func:`std::ostream& cvc5::operator<< (std::ostream& out, const std::vector<Term>& vector)`
- :cpp:func:`std::ostream& cvc5::operator<< (std::ostream& out, const std::set<Term>& set)`
- :cpp:func:`std::ostream& cvc5::operator<< (std::ostream& out, const std::unordered_set<Term>& set)`
- :cpp:func:`template<typename V> std::ostream& cvc5::operator<< (std::ostream& out, const std::map<Term, V>& map)`
- :cpp:func:`template<typename V> std::ostream& cvc5::operator<< (std::ostream& out, const std::unordered_map<Term, V>& map)`
- :cpp:struct:`std::hash\<cvc5::Term>`

----

.. doxygenclass:: cvc5::Term
    :project: cvc5
    :members:
    :undoc-members:

----

.. doxygenfunction:: cvc5::operator<<(std::ostream& out, const Term& t)
    :project: cvc5

.. doxygenfunction:: cvc5::operator<<(std::ostream& out, const std::vector<Term>& vector)
    :project: cvc5

.. doxygenfunction:: cvc5::operator<<(std::ostream& out, const std::set<Term>& set)
    :project: cvc5

.. doxygenfunction:: cvc5::operator<<(std::ostream& out, const std::unordered_set<Term>& set)
    :project: cvc5

.. doxygenfunction:: cvc5::operator<<(std::ostream& out, const std::map<Term, V>& map)
    :project: cvc5

.. doxygenfunction:: cvc5::operator<<(std::ostream& out, const std::unordered_map<Term, V>& map)
    :project: cvc5

----

.. doxygenstruct:: std::hash< cvc5::Term >
    :project: std
    :members:
    :undoc-members:
