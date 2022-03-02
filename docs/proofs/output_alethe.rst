Proof format: Alethe
====================

Using the flag --proof-format-mode=alethe, cvc5 can output proofs in the Alethe proof format that is described in detail here: https://verit.loria.fr/documentation/alethe-spec.pdf.

Additonally, the following flags should be used to produce proofs with a minimal number of holes in them and to avoid sharing that is not supported yet: --simplification=none --dag-thres=0 --proof-granularity=dsl-rewrite.

Currently, the theory of equality with uninterpreted functions, parts of the theory of arithmetic and parts of the theory of quantifiers are supported.
