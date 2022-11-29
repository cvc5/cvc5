Kind
================

Every :py:class:`Term <cvc5.Term>` has a kind which represents its type, for
example whether it is an equality (:py:obj:`Equal <cvc5.Kind.Equal>`), a
conjunction (:py:obj:`And <cvc5.Kind.And>`), or a bit-vector addtion
(:py:obj:`BVAdd <cvc5.Kind.BVAdd>`).
The kinds below directly correspond to the enum values of the C++ :cpp:enum:`Kind <cvc5::Kind>` enum.

.. autoclass:: cvc5.Kind
    :members:
    :undoc-members:
