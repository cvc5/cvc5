Proof format: Alethe
====================

Using the flag :ref:`proof-format-mode=alethe <lbl-option-proof-format-mode>`, cvc5 outputs proofs in the `Alethe proof format <https://verit.loria.fr/documentation/alethe-spec.pdf>`_.

Additonally, the following flags should be used to produce proofs without term sharing (which is not supported for the Alethe backend yet): :ref:`--simplification=none <lbl-option-simplification>` :ref:`--dag-thresh=0 <lbl-option-dag-thresh>`.

Currently, only the theory of equality with uninterpreted functions, parts of the theory of arithmetic and parts of the theory of quantifiers are supported.
