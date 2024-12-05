Proof format: Cooperating Proof Calculus
========================================

Using option :ref:`proof-format-mode=cpc <lbl-option-proof-format-mode>`, cvc5
outputs proofs in the Cooperating Proof Calculus proof format.

This calculus was designed to faithfully represent cvc5's internal reasoning.
As a disclaimer, this means that it treats certain operators differently from
the SMT-LIB standard.
As an example, cvc5 uses mixed arithmetic internally, where integers and reals
can appear together.
A comprehensive list of these differences can be found in the Eunoia definition
of CPC, as described below.

`Ethos <https://github.com/cvc5/ethos>`_ is an efficient proof checker written
in C++ which can check proofs in the CPC format.
For a quick start, the cvc5 repository contains a
:cvc5repo:`script <contrib/get-ethos-checker>` to download and install
the Ethos checker, and create scripts for generating proofs with cvc5 and
checking them with the Ethos proof checker.

The Ethos checker is based on the logical framework Eunoia.
The Cooperating Proof Calculus has been formalized in a Eunoia signature, which
is contained within the cvc5 repository in this
:cvc5repo:`file <proofs/eo/cpc/Cpc.eo>`.
Based on this signature, Ethos can check CPC proofs over all theories that are
formalized in this signature.
For more details on Eunoia and a comprehensive overview of the language
supported by the Ethos checker, see the user manual
`here <https://github.com/cvc5/ethos/blob/main/user_manual.md>`_.

Note that several proof rules in the Cooperating Proof Calculus are not yet
supported in Eunoia signatures. 
Steps that use such rules are printed as `trust` steps in the proof.
A trust step proves an arbitrary formula with no provided justification.
The resulting proof contains warnings for trust steps that indicate which
internal proof rules were recorded as trust steps in the proof.

Upon successful exit, `ethos` will return the output `incomplete` if any trust
step is used in the proof, indicating that the reasoning in the proof was
incomplete.
Otherwise, if all proof steps are fully specified, `ethos` will return the
output `correct`.
All proofs in the cpc format are closed refutations of the input, in that the
proof will assume formulas from the input and end with a step proving false.

For more fine-grained proofs, the additional option
:ref:`proof-granularity=dsl-rewrite <lbl-option-proof-granularity>` can be
passed to cvc5.
This will result in proofs with more detail.

A simple example of cvc5 producing a proof in CPC proof format is shown below.
Notice that the concrete syntax of CPC is very similar to the Alethe format.
However, the proof rules used by these two formats are different.

.. run-command:: bin/cvc5 --dump-proofs --proof-format-mode=cpc --proof-granularity=dsl-rewrite ../test/regress/cli/regress0/proofs/qgu-fuzz-1-bool-sat.smt2
