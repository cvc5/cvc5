Datatype
========

This class represents a datatype. A :cpp:class:`cvc5::Datatype` is encapsulated
by a datatype :cpp:class:`Sort <cvc5::Sort>` and can be retrieved from a
datatype sort via :cpp:func:`cvc5::Sort::getDatatype()`.
Datatypes are specified by a :cpp:class:`cvc5::DatatypeDecl` via
:cpp:func:`cvc5::TermManager::mkDatatypeDecl()` when constructing a datatype
sort.

----

- class :cpp:class:`cvc5::Datatype`
- :cpp:func:`std::ostream& cvc5::operator<< (std::ostream& out, const Datatype& dt)`

----

.. doxygenclass:: cvc5::Datatype
    :project: cvc5
    :members:
    :undoc-members:

----

.. doxygenfunction:: cvc5::operator<<(std::ostream& out, const Datatype& dt)
    :project: cvc5
