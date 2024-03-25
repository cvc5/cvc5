C++ API
=====================

The C++ API is the primary interface for cvc5 and exposes the full functionality of cvc5.
The :doc:`quickstart guide <quickstart>` gives a short introduction, while the following class hierarchy of the ``cvc5`` namespace provides more details on the individual classes.
For most applications, the :cpp:class:`Solver <cvc5::Solver>` class is the main entry point to cvc5.


.. container:: hide-toctree

  .. toctree::

    quickstart
    exceptions
    datatype
    datatypeconstructor
    datatypeconstructordecl
    datatypedecl
    datatypeselector
    driveroptions
    grammar
    kind
    modes
    op
    optioninfo
    result
    roundingmode
    solver
    sort
    sortkind
    statistics
    synthresult
    term
    termmanager
    unknownexplanation


Class hierarchy
^^^^^^^^^^^^^^^

``namespace cvc5 {``

  * class :cpp:class:`CVC5ApiException <cvc5::CVC5ApiException>`
  * class :cpp:class:`CVC5ApiRecoverableException <cvc5::CVC5ApiRecoverableException>`
  * class :ref:`api/cpp/datatype:datatype`

    * class :cpp:class:`const_iterator <cvc5::Datatype::const_iterator>`

  * class :ref:`api/cpp/datatypeconstructor:datatypeconstructor`

    * class :cpp:class:`const_iterator <cvc5::DatatypeConstructor::const_iterator>`

  * class :ref:`api/cpp/datatypeconstructordecl:datatypeconstructordecl`
  * class :ref:`api/cpp/datatypedecl:datatypedecl`
  * class :ref:`api/cpp/datatypeselector:datatypeselector`
  * class :ref:`api/cpp/driveroptions:driveroptions`
  * class :ref:`api/cpp/grammar:grammar`
  * class :ref:`api/cpp/op:op`
  * class :ref:`api/cpp/optioninfo:optioninfo`
  * class :ref:`api/cpp/result:result`
  * class :ref:`api/cpp/termmanager:termmanager`
  * class :ref:`api/cpp/solver:solver`
  * class :ref:`api/cpp/sort:sort`
  * class :cpp:class:`Stat <cvc5::Stat>`
  * class :cpp:class:`Statistics <cvc5::Statistics>`
  * class :ref:`api/cpp/synthresult:synthresult`
  * class :ref:`api/cpp/term:term`

    * class :cpp:class:`const_iterator <cvc5::Term::const_iterator>`

  * enum class :ref:`api/cpp/kind:kind`
  * enum class :ref:`api/cpp/sortkind:sortkind`
  * enum class :ref:`api/cpp/roundingmode:roundingmode`
  * enum class :ref:`api/cpp/unknownexplanation:unknownexplanation`

``namespace modes {``
  * enum classes for :ref:`configuration modes<api/cpp/modes:modes>`

    * enum class for :cpp:enum:`cvc5::modes::BlockModelsMode`
    * enum class for :cpp:enum:`cvc5::modes::LearnedLitType`
    * enum class for :cpp:enum:`cvc5::modes::ProofComponent`
    * enum class for :cpp:enum:`cvc5::modes::FindSynthTarget`
``}``

``namespace parser {``

  * class :cpp:class:`Command <cvc5::parser::Command>`
  * class :ref:`api/cpp/inputparser:inputparser`
  * class :cpp:class:`ParserException <cvc5::parser::ParserException>`
  * class :cpp:class:`SymbolManager <cvc5::parser::SymbolManager>`
``}``

``}``
