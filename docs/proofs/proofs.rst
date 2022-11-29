Proof production
================

cvc5 produces proofs in an internal proof calculus that faithfully reflects its
reasoning. Here is a comprehensive description of the :doc:`proof rules
<proof_rules>`.

.. toctree::
   :hidden:

   proof_rules

Optionally cvc5 can convert and output its internal proofs into the following
external formats:

.. toctree::
   :maxdepth: 1

   Alethe <output_alethe>
   LFSC <output_lfsc>
   DOT <output_dot>

where note that the DOT format is only meant for visualization.
