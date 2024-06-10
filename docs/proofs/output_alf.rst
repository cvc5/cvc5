Proof format: AletheLF
======================

Using the flag :ref:`proof-format-mode=alf <lbl-option-proof-format-mode>`, cvc5 outputs proofs in the AletheLF (ALF) proof format.

The ALF proof format is based on the SMT-LIB 3 language. An efficient C++ proof checker for ALF is available `here <https://github.com/cvc5/alfc>`_. For details on the checker and a comprehensive overview of the AletheLF language supported by the checker, see the user manual `here <https://github.com/cvc5/alfc/blob/main/user_manual.md>`_.

For a quick start, the cvc5 repository contains a :cvc5repo:`script <contrib/get-alf-checker>` which will download and install the ALF proof checker (alfc), and create scripts for generating proofs with cvc5 and checking them with the ALF proof checker.

The AletheLF language is a meta-framework, meaning that the proof rules used by cvc5 are defined in signature files.   The signature files are contained within the cvc5 repository in this :cvc5repo:`directory <proofs/alf/cvc5/Cvc5.smt3>`. Based on these signatures, cvc5 provides basic support for ALF proofs over all theories that it supports.

Note that several proof rules in the internal calculus are not yet supported in ALF signatures.  Steps that use such rules are printed as `trust` steps in the ALF proof. A trust step proves an arbitrary formula with no provided justification. The ALF proof contains warnings for trust steps that indicate which internal proof rules were recorded as trust steps in the ALF proof.

To get more fine-grained proofs, the additional option :ref:`proof-granularity=theory-rewrite <lbl-option-proof-granularity>` can be passed to cvc5. This often will result in ALF proofs with more detail, and whose trust steps correspond only to equalities corresponding to theory rewrites.

A simple example of cvc5 producing a proof in ALF proof format:

.. run-command:: bin/cvc5 --dump-proofs --proof-format-mode=alf --proof-granularity=theory-rewrite ../test/regress/cli/regress0/proofs/qgu-fuzz-1-bool-sat.smt2
