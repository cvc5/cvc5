DatatypeConstructor
===================

This class represents a datatype constructor. Datatype constructors are
specified by a :py:obj:`cvc5.DatatypeConstructorDecl` via
:py:func:`cvc5.TermManager.mkDatatypeConstructorDecl()` when constructing a
datatype sort and can be retrieved from a :py:obj:`cvc5.Datatype` via
:py:func:`cvc5.Datatype.getConstructor()`.

----

.. autoclass:: cvc5.DatatypeConstructor
    :members:
    :special-members: __getitem__, __iter__
    :undoc-members:
