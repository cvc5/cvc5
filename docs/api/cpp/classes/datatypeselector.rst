DatatypeSelector
================

This class represents a datatype selector. Datatype selectors are
specified via :cpp:func:`cvc5::DatatypeConstructorDecl::addSelector()` when
constructing a datatype sort and can be retrieved from a
:cpp:class:`cvc5::DatatypeConstructor` via
:cpp:func:`cvc5::DatatypeConstructor::getSelector()`.

----

- class :cpp:class:`cvc5::DatatypeSelector`
- :cpp:func:`std::ostream& cvc5::operator<< (std::ostream& out, const DatatypeSelector& sel)`

----

.. doxygenclass:: cvc5::DatatypeSelector
    :project: cvc5
    :members:
    :undoc-members:

----

.. doxygenfunction:: cvc5::operator<<(std::ostream& out, const DatatypeSelector& sel)
    :project: cvc5
