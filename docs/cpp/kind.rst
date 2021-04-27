Kind
====

Every :cpp:class:`Term <cvc5::api::Term>` has a kind which represents its type,
for example whether it is an equality (:cpp:enumerator:`EQUAL
<cvc5::api::Kind::EQUAL>`), a conjunction (:cpp:enumerator:`AND
<cvc5::api::Kind::AND>`), or a bitvector addition
(:cpp:enumerator:`BITVECTOR_PLUS <cvc5::api::Kind::BITVECTOR_PLUS>`).
#ifndef DOXYGEN_SKIP
Note that the API type :cpp:enum:`cvc5::api::Kind` roughly corresponds to
:cpp:enum:`cvc5::Kind`, but is a different type. It hides internal kinds that
should not be exported to the API, and maps all kinds that we want to export
to its corresponding internal kinds.
#endif

.. doxygenenum:: cvc5::api::Kind
    :project: cvc5

.. doxygenstruct:: std::hash< cvc5::api::Kind >
    :project: std
    :members:
    :undoc-members:
