Op
================

This class encapsulates a cvc5 operator. A :py:obj:`cvc5.Op` is a term that
represents an operator, instantiated with the parameters it requires (if any).

A :py:obj:`cvc5.Term` of operator kind that does not require additional
parameters, e.g., :py:obj:`cvc5.Kind.ADD`, is usually constructed via
:py:func:`cvc5.Solver.mkTerm(Kind kind, const std.vector\<Term>& children) <Term cvc5.Solver.mkTerm(Kind kind, const std.vector\<Term>& children) const>`.
Alternatively, any :py:obj:`cvc5.Term` can be constructed via first
instantiating a corresponding :py:obj:`cvc5.Op`, even if the operator does
not require additional parameters.
Terms with operators that require additional parameters, e.g.,
:py:obj:`cvc5.Kind.BITVECTOR_EXTRACT`, must be created via
:py:func:`cvc5.TermManager.mkOp()` and :py:func:`cvc5.TermManager.mkTerm()`.

----

.. autoclass:: cvc5.Op
    :members:
    :special-members: __getitem__
    :undoc-members:
