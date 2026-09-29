Kind
================

Every :py:obj:`Term <cvc5.Term>` has an associated kind, represented
as enum class :py:obj:`cvc5.Kind`.
This kind distinguishes if the Term is a value, constant, variable or operator,
and what kind of each.
For example, a bit-vector value has kind
:py:obj:`CONST_BITVECTOR <cvc5.Kind.CONST_BITVECTOR>`,
a free constant symbol has kind
:py:obj:`CONSTANT <cvc5.Kind.CONSTANT>`,
an equality over terms of any sort has kind
:py:obj:`EQUAL <cvc5.Kind.EQUAL>`, and a universally
quantified formula has kind :py:obj:`FORALL <cvc5.Kind.FORALL>`.

The kinds below directly correspond to the enum values of the C++
:cpp:enum:`Kind <cvc5::Kind>` enum.

----

.. autoclass:: cvc5.Kind
    :members:
    :undoc-members:
