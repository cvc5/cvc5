Proof Rules
===========

This section introduces two enumerations: :cpp:enum:`ProofRule <cvc5::ProofRule>` and :cpp:enum:`ProofRewriteRule <cvc5::ProofRewriteRule>`.

The :cpp:enum:`ProofRule <cvc5::ProofRule>` enumeration captures the reasoning steps performed by the SAT and theory solvers. It represents the inference rules used to derive conclusions within a proof.

Conversely, the :cpp:enum:`ProofRewriteRule <cvc5::ProofRewriteRule>` enumeration pertains to the pre-processing performed on terms. It represents the rewrites that are applied to terms to simplify or transform them before they are sent to the solvers for reasoning.

.. doxygenenum:: cvc5::ProofRule
    :project: cvc5

.. doxygenenum:: cvc5::ProofRewriteRule
    :project: cvc5
