ProofRule and ProofRewriteRule
==============================

Enum :py:obj:`ProofRule <cvc5.ProofRule>` captures the reasoning steps
performed by the SAT solver, the theory solvers and the preprocessor. It
represents the inference rules used to derive conclusions within a proof.

Enum :py:obj:`ProofRewriteRule <cvc5.ProofRewriteRule>` pertains to
rewrites performed on terms. These identifiers are arguments of the proof rules
:py:obj:`THEORY_REWRITE <cvc5.ProofRule.THEORY_REWRITE>` and
:py:obj:`DSL_REWRITE <cvc5.ProofRule.DSL_REWRITE>`.

----

.. autoclass:: cvc5.ProofRule
    :members:
    :undoc-members:

----

.. autoclass:: cvc5.ProofRewriteRule
    :members:
    :undoc-members:

----

Enum :py:obj:`AnnotationId <cvc5.AnnotationId>` is used as an argument of the
proof rule :py:obj:`ANNOTATE <cvc5.ProofRule.ANNOTATE>`. It is experimental and
may change in future versions.

.. autoclass:: cvc5.AnnotationId
    :members:
    :undoc-members:
