Proof
=====

This class encapsulates a cvc5 proof object, which can be retrieved via
function :cpp:func:`cvc5::Solver::getProof()` after a
:cpp:func:`cvc5::Solver::checkSat()` query returns an `unsat` result.

----

- class :cpp:class:`cvc5::Proof`
- :cpp:func:`cvc5::Solver::proofToString()`
- :cpp:struct:`std::hash\<cvc5::Term>`

----

.. doxygenclass:: cvc5::Proof
    :project: cvc5
    :members:
    :undoc-members:

----

.. doxygenstruct:: std::hash< cvc5::Proof >
    :project: std
    :members:
    :undoc-members:
