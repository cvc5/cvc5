Kind
================

Every :py:class:`Term <pycvc5.Term>` has a kind which represents its type, for
example whether it is an equality (:py:obj:`Equal <pycvc5.Kind.Equal>`), a
conjunction (:py:obj:`And <pycvc5.Kind.And>`), or a bit-vector addtion
(:py:obj:`BVAdd <pycvc5.Kind.BVAdd>`).
The kinds below directly correspond to the enum values of the C++ :cpp:enum:`Kind <cvc5::api::Kind>` enum.

.. autoclass:: pycvc5.Kind
    :members:
    :undoc-members:
