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

Checking with Logos
-------------------

`Logos <https://github.com/cvc5/logos>`_ is an alternative checker for the
CPC format, written in Lean, whose soundness is proven against a formalization
of the semantics of SMT-LIB.
It accepts the same proof syntax as Ethos, but does not read Eunoia
signatures.
Instead, its proof rules are not written by hand: they are compiled from the
same Eunoia definition of CPC that is contained in this repository, so that the
proof rules of the two checkers come from a single definition.
The cvc5 repository contains a
:cvc5repo:`script <contrib/get-logos-checker>` to download and install the
Logos checker, and create scripts for generating proofs with cvc5 and checking
them with the Logos proof checker.

Logos targets the fragment of CPC that is used by safe builds of cvc5, that is,
builds configured with ``./configure.sh safe-mode``.
The expert CPC rules that may be used by non-safe builds lie outside that
fragment, as do the SMT-LIB input features that Logos does not model; which
features those are is documented in Logos itself.
For an input outside its scope, Logos reports ``incomplete``.
This means that the proof of correctness for Logos does not cover that input;
it does not mean that Logos found the CPC proof to be incorrect.
Because the CI of cvc5 requires proofs in safe mode to be complete, that is,
free of trust steps, every proof rule that a safe build can use is one that
Logos verifies, apart from inputs of the kind just described.

Keeping CPC and Logos in sync
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

Since that compilation consumes the signature in this repository, a change to
:cvc5repo:`proofs/eo/cpc <proofs/eo/cpc>` must remain in sync with Logos.
The commit of Logos this repository is pinned to is ``LOGOS_VERSION`` in
:cvc5repo:`contrib/get-logos-checker <contrib/get-logos-checker>`, which is the
only place it appears.
The :cvc5repo:`script <contrib/check-logos-compilation>`
``contrib/check-logos-compilation`` reads that pin, sets up the Eunoia
compiler that performs the compilation, and reports whether the signature
still compiles and whether that pinned Logos was generated from the current
version of it.
This check does not build Logos or check its Lean proofs.
The ``cpc-logos`` workflow additionally requires that the CI of Logos has
passed at the pinned commit, which it establishes by querying the result
already recorded for that commit rather than by rerunning that CI.

These two conditions together, that the pinned Logos was generated from the
signature in this repository and that the CI of Logos passes at that commit,
are what makes the Eunoia definition of CPC here correct with respect to the
semantics of SMT-LIB formalized in Logos, up to what that CI tests.
Neither condition suffices on its own: a Logos that passes its CI says nothing
about a signature it was not generated from, and a Logos generated from the
current signature says nothing until its Lean proofs have been checked.

Changing the CPC signature
^^^^^^^^^^^^^^^^^^^^^^^^^^

Adding a proof rule to :cvc5repo:`proofs/eo/cpc <proofs/eo/cpc>`, or removing
one, therefore requires a matching change to Logos: the Lean proof of that rule
is written or removed there, and ``LOGOS_VERSION`` is then moved to the
resulting commit, which moves both the checker that is installed and the
checker that CPC is checked against.
Logos is regenerated and repaired against a new version of the signature by the
`procedure documented there
<https://github.com/cvc5/logos#regenerating-the-calculus>`_.
Until the pin is moved, the ``cpc-logos`` workflow fails on the cvc5 pull
request that changes the signature.

A rule that is needed in cvc5 but cannot readily be proven in Logos does not
have to hold up that pull request.
Two ways of proceeding keep the pin movable:

- Demote the option that gives rise to the rule to unrestricted mode, so that
  the rule falls outside the fragment of CPC that Logos covers.

- Keep the option in safe mode and have Logos leave the rule out of the
  compilation, which its configuration of CPC provides for.
  This unblocks the pin without extending the guarantee above: a proof that
  uses such a rule is reported ``incomplete``, as for any other input outside
  the scope of Logos.
