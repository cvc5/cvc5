Kind
================

Every :py:class:`Term <pycvc5.Term>` has a kind which represents its type, for
example whether it is an equality (:py:obj:`Equal <pycvc5.kinds.Equal>`), a
conjunction (:py:obj:`And <pycvc5.kinds.And>`), or a bit-vector addtion
(:py:obj:`BVAdd <pycvc5.kinds.BVAdd>`).
The kinds below directly correspond to the enum values of the C++ :cpp:enum:`Kind <cvc5::api::Kind>` enum.

.. autoclass:: pycvc5.kinds
    :members:
    :undoc-members:
