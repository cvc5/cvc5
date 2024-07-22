Proof Production
================

cvc5 produces proofs in a proof calculus that faithfully reflects its
reasoning. The calculus is called the Cooperating Proof Calculus (CPC).
cvc5 supports retrieving a proof object via the API
(see how these objects are defined in :doc:`C++ <../api/cpp/classes/proof>`,
:doc:`C <../api/c/types/cvc5proof>`,
`Java <../api/../api/java/io/github/cvc5/Proof.html>`_,
:doc:`Base Python <../api/python/base/proof>`).


Proof Rules
^^^^^^^^^^^

A comprehensive description of the **proof rules** of the Cooperating Proof
Calculus can be found here:

* :doc:`C++ API <../api/cpp/enums/proofrule>`

* :doc:`C API <../api/c/enums/cvc5proofrule>`

* **Java API**

  * enum `ProofRule <../api/java/io/github/cvc5/ProofRule.html>`_
  * enum `ProofRewriteRule <api/java/io/github/cvc5/ProofRewriteRule.html>`_

* :doc:`Base Python API <../api/python/base/proofrule>`

.. toctree::
   :hidden:

   Proof Rules (C++) <../api/cpp/enums/proofrule>
   Proof Rules (C) <../api/c/enums/cvc5proofrule>
   Proof Rules (Python) <../api/python/base/proofrule>


Proof Formats
-------------

Optionally, cvc5 allows to convert and output its internal proofs into the
following external formats.

.. toctree::
   :maxdepth: 1

   CPC <output_cpc>
   Alethe <output_alethe>
   LFSC <output_lfsc>
   DOT <output_dot>

Note that the DOT format is only meant for visualization.
