Solver
======

This class represents a cvc5 solver instance.

:cpp:class:`Terms <cvc5::Term>`, :cpp:class:`Sorts <cvc5::Sort>` and
:cpp:class:`Ops <cvc5::Op>` are not tied to a :cpp:class:`cvc5::Solver`
but associated with a :cpp:class:`cvc5::TermManager` instance, which can be
shared between solver instances.

Solver options are configured via :cpp:func:`cvc5::Solver::setOption()`
and queried via :cpp:func:`cvc5::Solver::getOption()`
(for more information on configuration options, see :doc:`../../options`).
Information about a specific option can be retrieved via
:cpp:func:`cvc5::getOptionInfo()` (see :doc:`optioninfo`).

----

.. doxygenclass:: cvc5::Solver
    :project: cvc5
    :members:
    :undoc-members:
