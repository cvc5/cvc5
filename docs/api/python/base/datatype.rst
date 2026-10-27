Datatype
========

This class represents a datatype. A :py:obj:`cvc5.Datatype` is encapsulated
by a datatype :py:obj:`Sort <cvc5.Sort>` and can be retrieved from a
datatype sort via :py:func:`cvc5.Sort.getDatatype()`.
Datatypes are specified by a :py:obj:`cvc5.DatatypeDecl` via
:py:func:`cvc5.TermManager.mkDatatypeDecl()` when constructing a datatype
sort.

----

.. autoclass:: cvc5.Datatype
    :members:
    :special-members: __getitem__, __iter__
    :undoc-members:
