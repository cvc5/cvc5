Kind
====

Every :cpp:class:`Term <cvc5::Term>` has an associated kind, represented
as enum class :cpp:enum:`cvc5::Kind`.
This kind distinguishes if the Term is a value, constant, variable or operator,
and what kind of each.
For example, a bit-vector value has kind
:cpp:enumerator:`CONST_BITVECTOR <cvc5::Kind::CONST_BITVECTOR>`,
a free constant symbol has kind
:cpp:enumerator:`CONSTANT <cvc5::Kind::CONSTANT>`,
an equality over terms of any sort has kind
:cpp:enumerator:`EQUAL <cvc5::Kind::EQUAL>`, and a universally
quantified formula has kind :cpp:enumerator:`FORALL <cvc5::Kind::FORALL>`.

----

- enum class :cpp:enum:`cvc5::Kind`
- :cpp:func:`std::ostream& cvc5::operator<< (std::ostream& out, Kind kind)`
- :cpp:func:`std::string std::to_string(cvc5::Kind kind)`
- :cpp:struct:`std::hash\<cvc5::Kind>`

----

.. doxygenenum:: cvc5::Kind
    :project: cvc5

----

.. doxygenfunction:: cvc5::operator<<(std::ostream& out, Kind kind)
    :project: cvc5

.. doxygenfunction:: std::to_string(cvc5::Kind kind)
    :project: cvc5

----

.. doxygenstruct:: std::hash< cvc5::Kind >
    :project: std
    :members:
    :undoc-members:
