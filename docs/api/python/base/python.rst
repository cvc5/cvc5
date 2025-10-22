Base Python API
========================

.. only:: not bindings_python

    .. warning::

        This documentation was built while python bindings were disabled.
        This part of the documentation is likely either empty or outdated.
        Please enable :code:`BUILD_BINDINGS_PYTHON` in :code:`cmake` and
        build the documentation again.

This is the base Python API.
It is implemented on top of the C++ API and mirrors the :doc:`C++ API
<../../cpp/cpp>`.

For a higher-level, more pythonic programming experience, cvc5 provides the
:doc:`pythonic API <../pythonic/pythonic>`.

.. toctree::
    :maxdepth: 1
    :hidden:

    quickstart
    command
    datatype
    datatypeconstructor
    datatypeconstructordecl
    datatypedecl
    datatypeselector
    grammar
    inputparser
    kind
    modes
    op
    plugin
    proof
    result
    roundingmode
    solver
    sort
    sortkind
    statistics
    symbolmanager
    synthresult
    term
    termmanager
    unknownexplanation

----

Classes
-------

- :doc:`command`
- :doc:`datatype`
- :doc:`datatypeconstructor`
- :doc:`datatypeconstructordecl`
- :doc:`datatypedecl`
- :doc:`datatypeselector`
- :doc:`grammar`
- :doc:`inputparser`
- :doc:`op`
- :doc:`plugin`
- :doc:`proof`
- :doc:`result`
- :doc:`solver`
- :doc:`sort`
- :doc:`statistics`
- :doc:`symbolmanager`
- :doc:`synthresult`
- :doc:`term`

Enums
-----

- :doc:`kind`
- :doc:`proofrule`
- :doc:`roundingmode`
- :doc:`unknownexplanation`

- enums for :doc:`configuration modes <modes>`

  - :py:obj:`BlockModelsMode <cvc5.BlockModelsMode>`
  - :py:obj:`LearnedLitType <cvc5.LearnedLitType>`
  - :py:obj:`OptionCategory <cvc5.OptionCategory>`
  - :py:obj:`ProofComponent <cvc5.ProofComponent>`
  - :py:obj:`ProofFormat <cvc5.ProofFormat>`

