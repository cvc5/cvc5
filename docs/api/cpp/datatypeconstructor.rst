DatatypeConstructor
===================

This class represents a datatype constructor. Datatype constructors are
specified via :cpp:class:`cvc5::DatatypeConstructorDecl` when constructing a
datatype sort and can be retrieved from a :cpp:class:`cvc5::Datatype` via
:cpp:func:`cvc5::Datatype::getConstructor()`.

----

- class :cpp:class:`cvc5::DatatypeConstructor`
- :cpp:func:`std::ostream& cvc5::operator<< (std::ostream& out, const DatatypeConstructor& cons)`

----

.. doxygenclass:: cvc5::DatatypeConstructor
    :project: cvc5
    :members:
    :undoc-members:

----

.. doxygenfunction:: cvc5::operator<<(std::ostream& out, const DatatypeConstructor& cons)
    :project: cvc5
