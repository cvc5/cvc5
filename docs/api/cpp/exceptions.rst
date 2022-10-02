Exceptions
==========

The cvc5 API communicates certain errors using exceptions. We broadly
distinguish two types of exceptions: :cpp:class:`CVC5ApiException
<cvc5::CVC5ApiException>` and :cpp:class:`CVC5ApiRecoverableException
<cvc5::CVC5ApiRecoverableException>` (which is derived from
:cpp:class:`CVC5ApiException <cvc5::CVC5ApiException>`).

If any method fails with a :cpp:class:`CVC5ApiRecoverableException
<cvc5::CVC5ApiRecoverableException>`, the solver behaves as if the failing
method was not called. The solver can still be used safely.

If, however, a method fails with a :cpp:class:`CVC5ApiException
<cvc5::CVC5ApiException>`, the associated object may be in an unsafe state
and it should no longer be used.


.. doxygenclass:: cvc5::CVC5ApiException
    :project: cvc5
    :members:
    :undoc-members:

.. doxygenclass:: cvc5::CVC5ApiRecoverableException
    :project: cvc5
    :members:
    :undoc-members:
