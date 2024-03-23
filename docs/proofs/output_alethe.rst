Proof format: Alethe
====================

**WARNING: This format is experimental on the main branch of cvc5. To use this format, the option --proof-alethe-experimental must be used, or otherwise an execption is thrown.**

Using the flag :ref:`proof-format-mode=alethe <lbl-option-proof-format-mode>`,
cvc5 outputs proofs in the `Alethe proof format
<https://verit.loria.fr/documentation/alethe-spec.pdf>`_. Additonally, the
following additional flags are currently required: :ref:`simplification=none
<lbl-option-simplification>`, and :ref:`proof-alethe-experimental`.
The first requirement is due to not yet supporting proofs with non-detailed steps.

The Alethe proof format is a flexible proof format for SMT solvers based on
SMT-LIB.  It includes both coarse- and fine-grained steps and was first
implemented in the veriT solver :cite:`Bouton2009`.  Alethe proofs can be
checked via reconstruction within Isabelle/HOL :cite:`Barbosa2020, Schurr2021`
as well as within Coq, the latter via the SMTCoq plugin :cite:`Armand2011,
Ekici2017`. There is also a high performance Rust proof checker for Alethe,
available `here <https://github.com/ufmg-smite/alethe-proof-checker>`_.

Currently, only the theory of equality with uninterpreted functions, parts of
the theory of arithmetic and parts of the theory of quantifiers are supported in
cvc5's Alethe proofs.

A simple example of cvc5 producing a proof in the Alethe proof format:

.. run-command:: bin/cvc5 --dump-proofs --proof-format-mode=alethe --simplification=none --proof-alethe-experimental ../test/regress/cli/regress0/proofs/qgu-fuzz-1-bool-sat.smt2
