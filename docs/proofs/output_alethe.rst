Proof format: Alethe
====================

Using the flag :ref:`proof-format-mode=alethe <lbl-option-proof-format-mode>`,
cvc5 outputs proofs in the `Alethe proof format
<https://verit.gitlabpages.uliege.be/alethe/specification.pdf>`_.

The Alethe proof format is a flexible proof format for SMT solvers based on
SMT-LIB.  It includes both coarse- and fine-grained steps and was first
implemented in the veriT solver :cite:`Bouton2009`.  Alethe proofs can be
checked via reconstruction within Isabelle/HOL :cite:`Barbosa2020, Schurr2021`
as well as within Coq, the latter via the SMTCoq plugin :cite:`Armand2011,
Ekici2017`. There is also a high performance Rust proof checker and elaborator
for Alethe: Carcara, available `here
<https://github.com/ufmg-smite/carcara>`_. For a quick start, the cvc5
repository contains a :cvc5repo:`script <contrib/get-carcara-checker>` to
download and install the Carcara checker's version with full support for cvc5
Alethe proofs, and create scripts for generating proofs with cvc5 and checking
them with Carcara.

Currently, the theories of equality with uninterpreted functions, linear
arithmetic, bit-vectors and parts of the theory of strings (with or without
quantifiers) are supported in cvc5's Alethe proofs.

A simple example of cvc5 producing a proof in the Alethe proof format:

.. run-command:: bin/cvc5 --dump-proofs --proof-format-mode=alethe ../test/regress/cli/regress0/proofs/qgu-fuzz-1-bool-sat.smt2
