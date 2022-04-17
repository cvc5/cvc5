Proof format: LFSC
==================

Using the flag :ref:`proof-format-mode=lfsc <lbl-option-proof-format-mode>`, cvc5 outputs proofs in the LFSC proof format.

The LFSC proof format is based on the LF logical framework extended with computational side conditions, as described in :cite:`DBLP:journals/fmsd/StumpORHT13`. A high performance C++ proof checker for LFSC is available `here <https://github.com/cvc5/LFSC>`_.

For a quick start, the cvc5 repository contains a :cvc5repo:`script <contrib/get-lfsc-checker>` which will download and install the LFSC proof checker, and create scripts for generating proofs with cvc5 and checking them with the LFSC proof checker.

LFSC is a meta-framework, meaning that the proof rules used by cvc5 are defined in signature files, also contained within the cvc5 repository in this :cvc5repo:`directory <proofs/lfsc/signatures>`. Based on these signatures, cvc5 provides basic support for LFSC proofs over all theories that it supports.

Note that several proof rules in the internal calculus are not yet supported in LFSC signatures, and are instead printed as `trust` steps in the LFSC proof. A trust step proves an arbitrary formula with no provided justification. The LFSC proof contains warnings for which proof rules from the internal calculus were recorded as trust steps in the LFSC proof.

For more fine-grained proofs, the additional option :ref:`proof-granularity=theory-rewrite <lbl-option-proof-granularity>` should be passed to cvc5. This often will result in LFSC proofs with more detail, and whose trust steps correspond only to equalities corresponding to theory rewrites.

A simple example of cvc5 producing a proof in LFSC proof format:

.. run-command:: bin/cvc5 --dump-proofs --proof-format-mode=lfsc --proof-granularity=theory-rewrite ../test/regress/cli/regress0/proofs/qgu-fuzz-1-bool-sat.smt2
