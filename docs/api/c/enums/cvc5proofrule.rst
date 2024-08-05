Cvc5ProofRule and Cvc5ProofRewriteRule
======================================

Enum :cpp:enum:`Cvc5ProofRule` captures the reasoning steps performed by the
SAT solver, the theory solvers and the preprocessor. It represents the
inference rules used to derive conclusions within a proof.

Enum :cpp:enum:`Cvc5ProofRewriteRule` pertains to rewrites performed on terms.
These identifiers are arguments of the proof rules
:cpp:enumerator:`CVC5_PROOF_RULE_THEORY_REWRITE` and
:cpp:enumerator:`CVC5_PROOF_RULE_DSL_REWRITE`.

----

.. doxygenenum:: Cvc5ProofRule
    :project: cvc5_c

.. doxygenfunction:: cvc5_proof_rule_to_string
    :project: cvc5_c

.. doxygenfunction:: cvc5_proof_rule_hash
    :project: cvc5_c

----

.. doxygenenum:: Cvc5ProofRewriteRule
    :project: cvc5_c

.. doxygenfunction:: cvc5_proof_rewrite_rule_to_string
    :project: cvc5_c

.. doxygenfunction:: cvc5_proof_rewrite_rule_hash
    :project: cvc5_c
