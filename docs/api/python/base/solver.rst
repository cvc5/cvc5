Solver
========

This class represents a cvc5 solver instance.

:py:obj:`Terms <cvc5.Term>`, :py:obj:`Sorts <cvc5.Sort>` and
:py:obj:`Ops <cvc5.Op>` are not tied to a :py:obj:`cvc5.Solver`
but associated with a :py:obj:`cvc5.TermManager` instance, which can be
shared between solver instances.

Solver options are configured via :py:func:`cvc5.Solver.setOption()`
and queried via :py:func:`cvc5.Solver.getOption()`
(for more information on configuration options, see :doc:`../../../options`).

----

.. autoclass:: cvc5.Solver
    :members:
    :undoc-members:
