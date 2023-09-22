Result
======

This class represents a :cpp:class:`cvc5::Solver` result.

A :cpp:class:`cvc5::Result` encapsulates a 3-valued solver result (sat, unsat,
unknown). Explanations for unknown results are represented as enum class
:cpp:enum:`cvc5::UnknownExplanation` and can be queried via
:cpp:func:`cvc5::Result::getUnknownExplanation()`.

----

- class :cpp:class:`cvc5::Result`
- :cpp:func:`std::ostream& cvc5::operator<< (std::ostream& out, const Result& r)`

----

.. doxygenclass:: cvc5::Result
    :project: cvc5
    :members:
    :undoc-members:

----

.. doxygenfunction:: cvc5::operator<<(std::ostream& out, const Result& r)
    :project: cvc5

