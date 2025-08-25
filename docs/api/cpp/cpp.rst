C++ API
=====================

The C++ API is the primary interface for cvc5 and exposes the full
functionality of cvc5.

The :doc:`quickstart guide <quickstart>` gives a short introduction, while the
following class hierarchy of the ``cvc5`` namespace provides more details on
the individual classes.
For most applications, the :cpp:class:`Solver <cvc5::Solver>` class is the main
entry point to cvc5.


.. container:: hide-toctree

  .. toctree::

    quickstart
    exceptions/exceptions
    classes/command
    classes/datatype
    classes/datatypeconstructor
    classes/datatypeconstructordecl
    classes/datatypedecl
    classes/datatypeselector
    classes/driveroptions
    classes/grammar
    classes/inputparser
    enums/kind
    enums/modes
    classes/op
    classes/optioninfo
    classes/plugin
    classes/proof
    classes/result
    enums/roundingmode
    classes/solver
    classes/sort
    enums/sortkind
    classes/statistics
    classes/symbolmanager
    classes/synthresult
    classes/term
    classes/termmanager
    enums/unknownexplanation


Class hierarchy
^^^^^^^^^^^^^^^

``namespace cvc5 {``
  * class :cpp:class:`CVC5ApiException <cvc5::CVC5ApiException>`
  * class :cpp:class:`CVC5ApiRecoverableException <cvc5::CVC5ApiRecoverableException>`

  * class :doc:`classes/datatype`

    * class :cpp:class:`const_iterator <cvc5::Datatype::const_iterator>`

  * class :doc:`classes/datatypeconstructor`

    * class :cpp:class:`const_iterator <cvc5::DatatypeConstructor::const_iterator>`

  * class :doc:`classes/datatypeconstructordecl`
  * class :doc:`classes/datatypedecl`
  * class :doc:`classes/datatypeselector`
  * class :doc:`classes/driveroptions`
  * class :doc:`classes/grammar`
  * class :doc:`classes/op`
  * class :doc:`classes/optioninfo`
  * class :doc:`classes/proof`
  * class :doc:`classes/result`
  * class :doc:`classes/plugin`
  * class :doc:`classes/termmanager`
  * class :doc:`classes/solver`
  * class :doc:`classes/sort`
  * class :cpp:class:`Stat <cvc5::Stat>`
  * class :doc:`classes/statistics`
  * class :doc:`classes/synthresult`
  * class :doc:`classes/term`

    * class :cpp:class:`const_iterator <cvc5::Term::const_iterator>`

  * enum class :doc:`enums/kind`
  * enum class :doc:`enums/sortkind`
  * enum class :doc:`enums/roundingmode`
  * enum class :doc:`enums/unknownexplanation`

  * enum classes for :doc:`proof rules <enums/proofrule>`

    * enum class :cpp:enum:`ProofRule <cvc5::ProofRule>`
    * enum class :cpp:enum:`ProofRewriteRule <cvc5::ProofRewriteRule>`

``namespace modes {``
  * enum classes for :doc:`configuration modes <enums/modes>`

    * enum class for :cpp:enum:`cvc5::modes::BlockModelsMode`
    * enum class for :cpp:enum:`cvc5::modes::LearnedLitType`
    * enum class for :cpp:enum:`cvc5::modes::FindSynthTarget`
    * enum class for :cpp:enum:`cvc5::modes::OptionCategory`
    * enum class for :cpp:enum:`cvc5::modes::ProofComponent`
    * enum class for :cpp:enum:`cvc5::modes::ProofFormat`

``}``

``namespace parser {``
  * class :cpp:class:`ParserException <cvc5::parser::ParserException>`

  * class :cpp:class:`Command <cvc5::parser::Command>`
  * class :doc:`classes/inputparser`
  * class :cpp:class:`SymbolManager <cvc5::parser::SymbolManager>`

``}``

``}``
