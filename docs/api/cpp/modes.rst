Modes
======

Some API functions require a configuration mode argument, e.g.,
:cpp:func:`cvc5::Solver::blockModel()`.
The following enum classes define such configuration modes.

----

- enum class :cpp:enum:`cvc5::modes::BlockModelsMode`
- :cpp:func:`std::ostream& cvc5::modes::operator<< (std::ostream& out, BlockModelsMode mode)`

- enum class :cpp:enum:`cvc5::modes::LearnedLitType`
- :cpp:func:`std::ostream& cvc5::modes::operator<< (std::ostream& out, LearnedLitType type)`

- enum class :cpp:enum:`cvc5::modes::ProofComponent`
- :cpp:func:`std::ostream& cvc5::modes::operator<< (std::ostream& out, ProofComponent pc)`

- enum class :cpp:enum:`cvc5::modes::FindSynthTarget`
- :cpp:func:`std::ostream& cvc5::modes::operator<< (std::ostream& out, FindSynthTarget target)`

----

.. doxygenenum:: cvc5::modes::BlockModelsMode
    :project: cvc5

.. doxygenfunction:: cvc5::modes::operator<<(std::ostream& out, BlockModelsMode mode)
    :project: cvc5

----

.. doxygenenum:: cvc5::modes::LearnedLitType
    :project: cvc5

.. doxygenfunction:: cvc5::modes::operator<<(std::ostream& out, LearnedLitType type)
    :project: cvc5

----

.. doxygenenum:: cvc5::modes::ProofComponent
    :project: cvc5

.. doxygenfunction:: cvc5::modes::operator<<(std::ostream& out, ProofComponent pc)
    :project: cvc5

----

.. doxygenenum:: cvc5::modes::FindSynthTarget
    :project: cvc5

.. doxygenfunction:: cvc5::modes::operator<<(std::ostream& out, FindSynthTarget target)
    :project: cvc5
