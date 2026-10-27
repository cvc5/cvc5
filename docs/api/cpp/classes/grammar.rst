Grammar
=======

This class encapsulates a SyGuS grammar. It is created via
:cpp:func:`cvc5::Solver::mkGrammar()` and allows to define a context-free
grammar of terms, according to the definition of grammars in the SyGuS IF 2.1
standard.

----

- class :cpp:class:`cvc5::Grammar`
- :cpp:func:`std::ostream& cvc5::operator<< (std::ostream& out, const Grammar& g)`

----

.. doxygenclass:: cvc5::Grammar
    :project: cvc5
    :members:
    :undoc-members:

----

.. doxygenfunction:: cvc5::operator<<(std::ostream& out, const Grammar& g)
    :project: cvc5
