Solver
======

This class represents a cvc5 solver instance.

:cpp:class:`Terms <cvc5::Term>`, :cpp:class:`Sorts <cvc5::Sort>` and
:cpp:class:`Ops <cvc5::Op>` are not tied to a :cpp:class:`cvc5::Solver`
instance and can be shared between instances.
Term kinds are defined via enum class :doc:`cvc5::Kind <kind>`, and sort kinds
via enum class :doc:`cvc5::SortKind <sortkind>`.

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
