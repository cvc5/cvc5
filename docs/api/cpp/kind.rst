Kind
====

Every :cpp:class:`Term <cvc5::Term>` has an associated kind.
This kind distinguishes if the Term is a value, constant, variable or operator,
and what kind of each.
For example, a bit-vector value has kind
:cpp:enumerator:`CONST_BITVECTOR <cvc5::Kind::CONST_BITVECTOR>`,
a free constant symbol has kind
:cpp:enumerator:`CONSTANT <cvc5::Kind::CONSTANT>`,
an equality over terms of any sort has kind
:cpp:enumerator:`EQUAL <cvc5::Kind::EQUAL>`, and a universally
quantified formula has kind :cpp:enumerator:`FORALL <cvc5::Kind::FORALL>`.

.. doxygenenum:: cvc5::Kind
    :project: cvc5

.. doxygenstruct:: std::hash< cvc5::Kind >
    :project: std
    :members:
    :undoc-members:
