Modes
======

Some API functions require a configuration mode argument, e.g.,
:cpp:func:`cvc5::Solver::blockModel()`.
The following enum classes define such configuration modes.

----

- enum class :cpp:enum:`cvc5::modes::BlockModelsMode`
- :cpp:func:`std::ostream& cvc5::modes::operator<< (std::ostream& out, BlockModelsMode mode)`
- :cpp:func:`std::string std::to_string(cvc5::modes::BlockModelsMode mode)`

- enum class :cpp:enum:`cvc5::modes::LearnedLitType`
- :cpp:func:`std::ostream& cvc5::modes::operator<< (std::ostream& out, LearnedLitType type)`
- :cpp:func:`std::string std::to_string(cvc5::modes::LearnedLitType type)`

- enum class :cpp:enum:`cvc5::modes::FindSynthTarget`
- :cpp:func:`std::ostream& cvc5::modes::operator<< (std::ostream& out, FindSynthTarget target)`
- :cpp:func:`std::string std::to_string(cvc5::modes::FindSynthTarget target)`

- enum class :cpp:enum:`cvc5::modes::OptionCategory`
- :cpp:func:`std::ostream& cvc5::modes::operator<< (std::ostream& out, OptionCategory category)`
- :cpp:func:`std::string std::to_string(cvc5::modes::OptionCategory category)`

- enum class :cpp:enum:`cvc5::modes::ProofComponent`
- :cpp:func:`std::ostream& cvc5::modes::operator<< (std::ostream& out, ProofComponent pc)`
- :cpp:func:`std::string std::to_string(cvc5::modes::ProofComponent component)`

- enum class :cpp:enum:`cvc5::modes::ProofFormat`
- :cpp:func:`std::ostream& cvc5::modes::operator<< (std::ostream& out, ProofFormat pc)`
- :cpp:func:`std::string std::to_string(cvc5::modes::ProofFormat format)`

----

.. doxygenenum:: cvc5::modes::BlockModelsMode
    :project: cvc5

.. doxygenfunction:: cvc5::modes::operator<<(std::ostream& out, BlockModelsMode mode)
    :project: cvc5

.. doxygenfunction:: std::to_string(cvc5::modes::BlockModelsMode mode)
    :project: cvc5

----

.. doxygenenum:: cvc5::modes::LearnedLitType
    :project: cvc5

.. doxygenfunction:: cvc5::modes::operator<<(std::ostream& out, LearnedLitType type)
    :project: cvc5

.. doxygenfunction:: std::to_string(cvc5::modes::LearnedLitType type)
    :project: cvc5

----

.. doxygenenum:: cvc5::modes::FindSynthTarget
    :project: cvc5

.. doxygenfunction:: cvc5::modes::operator<<(std::ostream& out, FindSynthTarget target)
    :project: cvc5

.. doxygenfunction:: std::to_string(cvc5::modes::FindSynthTarget target)
    :project: cvc5

----

.. doxygenenum:: cvc5::modes::OptionCategory
    :project: cvc5

.. doxygenfunction:: cvc5::modes::operator<<(std::ostream& out, OptionCategory category)
    :project: cvc5

.. doxygenfunction:: std::to_string(cvc5::modes::OptionCategory category)
    :project: cvc5

----

.. doxygenenum:: cvc5::modes::ProofComponent
    :project: cvc5

.. doxygenfunction:: cvc5::modes::operator<<(std::ostream& out, ProofComponent pc)
    :project: cvc5

.. doxygenfunction:: std::to_string(cvc5::modes::ProofComponent component)
    :project: cvc5

----

.. doxygenenum:: cvc5::modes::ProofFormat
    :project: cvc5

.. doxygenfunction:: cvc5::modes::operator<<(std::ostream& out, ProofFormat pc)
    :project: cvc5

.. doxygenfunction:: std::to_string(cvc5::modes::ProofFormat format)
    :project: cvc5

