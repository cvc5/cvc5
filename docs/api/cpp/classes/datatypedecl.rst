DatatypeDecl
============

This class encapsulates a datatype declaration. A datatype declaration is
constructed via :cpp:func:`cvc5::Solver::mkDatatypeDecl()`. This is not a
datatype itself (see :doc:`datatype`), but the representation of the
specification for creating a datatype :cpp:class:`Sort <cvc5::Sort>` (see
:cpp:func:`cvc5::Solver::mkDatatypeSort()` and
:cpp:func:`cvc5::Solver::mkDatatypeSorts()`).


----

- class :cpp:class:`cvc5::DatatypeDecl`
- :cpp:func:`std::ostream& cvc5::operator<< (std::ostream& out, const DatatypeDecl& decl)`

----

.. doxygenclass:: cvc5::DatatypeDecl
    :project: cvc5
    :members:
    :undoc-members:

----

.. doxygenfunction:: cvc5::operator<<(std::ostream& out, const DatatypeDecl& decl)
    :project: cvc5
