Exceptions
==========

The CVC5 API communicates certain errors using exceptions.
We broadly distinguish two types of exceptions: :cpp:class:`CVC4ApiException <cvc5::api::CVC4ApiException>` and :cpp:class:`CVC4ApiRecoverableException <cvc5::api::CVC4ApiRecoverableException>` (which is derived from :cpp:class:`CVC4ApiException <cvc5::api::CVC4ApiException>`).

If any method fails with a :cpp:class:`CVC4ApiRecoverableException <cvc5::api::CVC4ApiRecoverableException>`, the solver behaves as if the failing method was not called. The solver can still be used safely.

If, however, a method fails with a :cpp:class:`CVC4ApiException <cvc5::api::CVC4ApiException>`, the associated object may be in an unsafe state and it should no longer be used.


.. doxygenclass:: cvc5::api::CVC4ApiException
    :project: cvc5
    :members:
    :undoc-members:

.. doxygenclass:: cvc5::api::CVC4ApiRecoverableException
    :project: cvc5
    :members:
    :undoc-members:
