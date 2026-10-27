DatatypeSelector
================

This class represents a datatype selector. Datatype selectors are
specified via :py:func:`cvc5.DatatypeConstructorDecl.addSelector()`,
:py:func:`cvc5.DatatypeConstructorDecl.addSelectorSelf()`
and :py:func:`cvc5.DatatypeConstructorDecl.addSelectorUnresolved()`
when constructing a datatype sort and can be retrieved from a
:py:obj:`cvc5.DatatypeConstructor` via
:py:func:`cvc5.DatatypeConstructor.getSelector()`.

----

.. autoclass:: cvc5.DatatypeSelector
    :members:
    :undoc-members:
