Proof Rules
===========

This section introduces two enumerations: :cpp:enum:`ProofRule <cvc5::ProofRule>` and :cpp:enum:`ProofRewriteRule <cvc5::ProofRewriteRule>`.

The :cpp:enum:`ProofRule <cvc5::ProofRule>` enumeration captures the reasoning steps performed by the SAT solver, the theory solvers or by the preprocessor. It represents the inference rules used to derive conclusions within a proof.

The :cpp:enum:`ProofRewriteRule <cvc5::ProofRewriteRule>` enumeration pertains to rewrites performed on terms. These identifiers are arguments of the proof rules :cpp:enumerator:`THEORY_REWRITE <cvc5::ProofRule::THEORY_REWRITE>` and :cpp:enumerator:`DSL_REWRITE <cvc5::ProofRule::DSL_REWRITE>`.

.. doxygenenum:: cvc5::ProofRule
    :project: cvc5

.. doxygenenum:: cvc5::ProofRewriteRule
    :project: cvc5
