DatatypeConstructorDecl
=======================

This class encapsulates a datatype constructor declaration. A datatype
constructor declaration is constructed via
:cpp:func:`cvc5::Solver::mkDatatypeConstructorDecl()`. This is not a
datatype itself (see :doc:`datatype`), but the representation of the
specification for creating a datatype constructor of a datatype
:cpp:class:`Sort <cvc5::Sort>` (see :cpp:func:`cvc5::Solver::mkDatatypeSort()`
and :cpp:func:`cvc5::Solver::mkDatatypeSorts()`).

----

- class :cpp:class:`cvc5::DatatypeConstructorDecl`
- :cpp:func:`std::ostream& cvc5::operator<< (std::ostream& out, const DatatypeConstructorDecl& decl)`
- :cpp:func:`std::ostream& cvc5::operator<< (std::ostream& out, const std::vector<DatatypeConstructorDecl>& vector)`

----

.. doxygenclass:: cvc5::DatatypeConstructorDecl
    :project: cvc5
    :members:
    :undoc-members:

----

.. doxygenfunction:: cvc5::operator<<(std::ostream& out, const DatatypeConstructorDecl& decl)
    :project: cvc5

.. doxygenfunction:: cvc5::operator<<(std::ostream& out, const std::vector<DatatypeConstructorDecl>& vector)
    :project: cvc5
