Statistics
==========

See :doc:`/statistics` for general information on statistics in cvc5.

Class :py:obj:`cvc5.Statistics` represents a mapping from statistic names
to statistic values

By default, iterating over a :py:obj:`Statistics <cvc5.Statistics>`
object shows all statistics, including internal and unchanged ones.
The inclusion of internal and defaulted statistics can be configured via
Boolean parameters ``internal`` and ``defaulted`` of function
:py:func:`cvc5.Statistics.get()`.

----

.. autoclass:: cvc5.Statistics
    :members:
    :special-members: __getitem__, __iter__, __next__
    :undoc-members:
