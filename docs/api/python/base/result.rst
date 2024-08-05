Result
================

This class represents a :py:obj:`cvc5.Solver` result.

A :py:obj:`cvc5.Result` encapsulates a 3-valued solver result (sat, unsat,
unknown). Explanations for unknown results are represented as enum
:py:obj:`cvc5.UnknownExplanation` and can be queried via
:py:func:`cvc5.Result.getUnknownExplanation()`.

----

.. autoclass:: cvc5.Result
    :members:
    :undoc-members:
