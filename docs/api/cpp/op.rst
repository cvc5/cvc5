Op
==

This class encapsulates a cvc5 operator. A :cpp:class:`cvc5::Op` is a term that
represents an operator, instantiated with the parameters it requires (if any).

A :cpp:class:`cvc5::Term` of operator kind that does not require additional
parameters, e.g., :cpp:enumerator:`cvc5::Kind::ADD`, is usually constructed via
:cpp:func:`cvc5::Solver::mkTerm(Kind kind, const std::vector\<Term>& children) <Term cvc5::Solver::mkTerm(Kind kind, const std::vector\<Term>& children) const>`.
Alternatively, any :cpp:class:`cvc5::Term` can be constructed via first
instantiating a corresponding :cpp:class:`cvc5::Op`, even if the operator does
not require additional parameters.
Terms with operators that require additional parameters, e.g.,
:cpp:enumerator:`cvc5::Kind::BITVECTOR_EXTRACT`, must be created via
:cpp:func:`cvc5::Solver::mkOp(Kind kind, const std::vector\<uint32_t> args) <cvc5::Solver::mkOp()>` and
:cpp:func:`cvc5::Solver::mkTerm(const Op& op, const std::vector\<Term>& children) <Term cvc5::Solver::mkTerm(const Op& op, const std::vector\<Term>& children) const>`.




----

- class :cpp:class:`cvc5::Op`
- :cpp:func:`std::ostream& cvc5::operator<< (std::ostream& out, const Op& op)`
- :cpp:struct:`std::hash\<cvc5::Op>`

----

.. doxygenclass:: cvc5::Op
    :project: cvc5
    :members:

----

.. doxygenfunction:: cvc5::operator<<(std::ostream& out, const Op& op)
    :project: cvc5

----

.. doxygenstruct:: std::hash< cvc5::Op >
    :project: std
    :members:
    :undoc-members:
