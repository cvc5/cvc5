Kind
====

Every :cpp:class:`Term <cvc5::api::Term>` has a kind which represents its type,
for example whether it is an equality (:cpp:enumerator:`EQUAL
<cvc5::api::Kind::EQUAL>`), a conjunction (:cpp:enumerator:`AND
<cvc5::api::Kind::AND>`), or a bitvector addition
(:cpp:enumerator:`BITVECTOR_PLUS <cvc5::api::Kind::BITVECTOR_PLUS>`).

Note that the api type :cpp:enum:`cvc5::api::Kind` roughly corresponds to
:cpp:enum:`cvc5::Kind`, but is a different type and has a few subtle
differences.


.. doxygenenum:: cvc5::api::Kind
    :project: cvc5

.. doxygenstruct:: cvc5::api::KindHashFunction
    :project: cvc5
    :members:
    :undoc-members:

