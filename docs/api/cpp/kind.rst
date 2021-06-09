Kind
====

Every :cpp:class:`Term <cvc5::api::Term>` has a kind which represents its type,
for example whether it is an equality (:cpp:enumerator:`EQUAL
<cvc5::api::Kind::EQUAL>`), a conjunction (:cpp:enumerator:`AND
<cvc5::api::Kind::AND>`), or a bit-vector addition
(:cpp:enumerator:`BITVECTOR_ADD <cvc5::api::Kind::BITVECTOR_ADD>`).

.. doxygenenum:: cvc5::api::Kind
    :project: cvc5

.. doxygenstruct:: std::hash< cvc5::api::Kind >
    :project: std
    :members:
    :undoc-members:
