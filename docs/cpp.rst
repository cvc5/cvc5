C++ API Documentation
=====================

Class Hierarchy
---------------

* namespace ``cvc5``

  * namespace ``api``

    * class :ref:`CVC4ApiException<exceptions>`

    * class :ref:`CVC4ApiRecoverableException<exceptions>`

    * class :doc:`cpp/datatype`

      * class :ref:`Datatype::const_iterator<datatype>`

    * class :doc:`cpp/datatypeconstructor`

      * class :ref:`DatatypeConstructor::const_iterator<datatypeconstructor>`

    * class :doc:`cpp/datatypeconstructordecl`

    * class :doc:`cpp/datatypedecl`

    * class :doc:`cpp/datatypeselector`

    * class :doc:`cpp/grammar`

    * class :doc:`cpp/op`

    * class :doc:`cpp/result`

    * class :doc:`cpp/solver`

    * class :doc:`cpp/term`

      * class :ref:`Term::const_iterator<term>`

    * enum :doc:`cpp/kind`

    * enum :doc:`cpp/roundingmode`

    * struct :ref:`KindHashFunction<kind>`

    * struct :ref:`OpHashFunction<op>`

    * struct :ref:`SortHashFunction<sort>`

    * struct :ref:`TermHashFunction<term>`


Full API Documentation
----------------------

Exceptions
^^^^^^^^^^
.. doxygenclass:: cvc5::api::CVC4ApiException
    :project: cvc5
    :members:

.. doxygenclass:: cvc5::api::CVC4ApiRecoverableException
    :project: cvc5
    :members:


Enums
^^^^^

.. toctree::
   :maxdepth: 2

   cpp/kind
   cpp/roundingmode


Classes
^^^^^^^

.. toctree::
   :maxdepth: 2

   cpp/datatype
   cpp/datatypeconstructor
   cpp/datatypeconstructordecl
   cpp/datatypedecl
   cpp/datatypeselector
   cpp/grammar
   cpp/op
   cpp/result
   cpp/solver
   cpp/sort
   cpp/term

