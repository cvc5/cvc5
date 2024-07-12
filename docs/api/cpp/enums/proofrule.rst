ProofRule and ProofRewriteRule
==============================

Enum class :cpp:enum:`ProofRule <cvc5::ProofRule>` captures the reasoning steps
performed by the SAT solver, the theory solvers and the preprocessor. It
represents the inference rules used to derive conclusions within a proof.

Enum class :cpp:enum:`ProofRewriteRule <cvc5::ProofRewriteRule>` pertains to
rewrites performed on terms. These identifiers are arguments of the proof rules
:cpp:enumerator:`THEORY_REWRITE <cvc5::ProofRule::THEORY_REWRITE>` and
:cpp:enumerator:`DSL_REWRITE <cvc5::ProofRule::DSL_REWRITE>`.

----

- enum class :cpp:enum:`cvc5::ProofRule`
- :cpp:func:`std::ostream& cvc5::operator<< (std::ostream& out, ProofRule pc)`
- :cpp:func:`std::string std::to_string(cvc5::ProofRule rule)`
- :cpp:struct:`std::hash\<cvc5::ProofRule>`

- enum class :cpp:enum:`cvc5::ProofRewriteRule`
- :cpp:func:`std::ostream& cvc5::operator<< (std::ostream& out, ProofRewriteRule pc)`
- :cpp:func:`std::string std::to_string(cvc5::ProofRewriteRule rule)`
- :cpp:struct:`std::hash\<cvc5::ProofRewriteRule>`

----

.. doxygenenum:: cvc5::ProofRule
    :project: cvc5

.. doxygenfunction:: cvc5::operator<<(std::ostream& out, ProofRule pc)
    :project: cvc5

.. doxygenfunction:: std::to_string(cvc5::ProofRule rule)
    :project: cvc5

.. doxygenstruct:: std::hash< cvc5::ProofRule >
    :project: std
    :members:
    :undoc-members:

----

.. doxygenenum:: cvc5::ProofRewriteRule
    :project: cvc5

.. doxygenfunction:: cvc5::operator<<(std::ostream& out, ProofRewriteRule pc)
    :project: cvc5

.. doxygenfunction:: std::to_string(cvc5::ProofRewriteRule rule)
    :project: cvc5

.. doxygenstruct:: std::hash< cvc5::ProofRewriteRule >
    :project: std
    :members:
    :undoc-members:
