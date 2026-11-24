DatatypeConstructorDecl
=======================

This class encapsulates a datatype constructor declaration.
A :py:obj:`DatatypeConstructorDecl <cvc5.DatatypeConstructorDecl>`
is constructed via :py:func:`cvc5.TermManager.mkDatatypeConstructorDecl()`.
This is not yet a :doc:`datatype constructor itself <datatypeconstructor>`,
but the representation of the specification for creating a datatype constructor
of a datatype :py:obj:`Sort <cvc5.Sort>` via
:py:func:`cvc5.TermManager.mkDatatypeSort()` and
:py:func:`cvc5.TermManager.mkDatatypeSorts()`.

----

.. autoclass:: cvc5.DatatypeConstructorDecl
    :members:
    :undoc-members:
