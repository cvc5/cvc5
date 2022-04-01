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
    statistics
    synthresult
    term
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
  * class :ref:`api/cpp/solver:solver`
  * class :ref:`api/cpp/sort:sort`
  * class :cpp:class:`Stat <cvc5::Stat>`
  * class :cpp:class:`Statistics <cvc5::Statistics>`
  * class :ref:`api/cpp/synthresult:synthresult`
  * class :ref:`api/cpp/term:term`

    * class :cpp:class:`const_iterator <cvc5::Term::const_iterator>`

  * enum :ref:`api/cpp/kind:kind`
  * enum :ref:`api/cpp/roundingmode:roundingmode`
  * enum :ref:`api/cpp/unknownexplanation:unknownexplanation`
  * modes enums :ref:`api/cpp/modes:modes`

``}``
