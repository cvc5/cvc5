This file contains a summary of important user-visible changes.

cvc5 1.0
=========

**New Features**

* *Streamlined C++ API*

* *Two new Python language bindings*
  - Base module: Feature complete with C++ API
  - Pythonic module: More pythonic bindings based on the base module

* *New Java language bindings*

* *Theory of Bags (Multisets)*
  - TODO: describe Bags

* *Theory of Sequences*
  - A new parametric theory of sequences whose syntax is compatible with the
    syntax for sequences used by Z3.
  - A new array-inspired procedure (option `--seq-array`).

* *Arithmetic*
  - Nonlinear real arithmetic is now solved using a new solver based on cylindrical
    algebraic coverings. Includes full support for non-rational models and a number
    of options `--nl-cov-*` for, e.g., different projection operators, Lazard's
    lifting or variable elimination.

* *Arrays*
  - Added support for an `eqrange` predicate. `(eqrange a b i j)` is true
    if arrays `a` and `b` are equal on all indices within indices `i` and `j`.

* *Bit-vectors*
  - New bit-vector solver with CaDiCaL as default SAT back-end.
  - New approach for solving bit-vectors as integers

* *Datatypes*
  - Support for generic datatype updaters `((_ update s) t u)` which replaces the field specified by selector `s` of `t` by the value `u`. 

* *Integers*
  - Support for an integer operator `(_ iand n)` that returns the bitwise `and`
    of two integers, seen as integers modulo n.
  - Support for an integer operator `int.pow2`, used as `(int.pow2 x)` which
    represents 2 to the power of x.

* *Quantifiers*
  - Get list of relevant Instantiations
  - Improved support for enumerative instantiation
  - SyGuS-based quantifier instantiation

* *Strings*
  - Improved performance using new techniques, including model-based reductions, eager context-dependent simplification, and equality-based conflict finding.
  - Support for `str.indexof_re(s, r, n)`, which returns the index of the first
    occurrence of a regular expression `r` in a string `s` after index `n` or
    -1 if `r` does not match a substring after `n`.

* *Proofs*
  * When used after an unsatisfiable response to checkSat, getProof
    returns a representation of the refutation proof for the current set of
    assertions (get-proof in SMT-LIB).

* *Difficulty Estimation*
  - The API method getDifficulty returns a map from asserted formulas to
    integers which estimates how much that formula contributed to the
    difficulty of the overall problem (get-difficulty in SMT-LIB).

* *Learned Literals*
  - The API method  getLearnedLiterals gets a list of literals that are
    entailed by the current set of assertions that were learned during solving
    (get-learned-literals in SMT-LIB).

* *Abduction and Interpolation*
  * The API method getAbduct can be used to find an abduct for the current set
    of assertions and provided goal (get-abduct in SMT-LIB). Optionally, a
    SyGuS grammar can be provided to restrict the shape of possible abducts.
    If using the text inferace, the grammar may be provided using the same
    syntax for grammars as in SyGuS IF format.
  * The API method getInterpolant can be used to find an interpolant for the
    current set of assertions and provided goal (get-interpolant in SMT-LIB).
    Like abduction, grammars may be provided to restrict the shape of
    interpolants.

* *Support for Incremental Synthesis Queries*
  - The core SyGuS solver now supports getting multiple solutions for a
    synthesis conjecture via the API. The method checkSynthNext finds the
    next SyGuS solution to the current set of SyGuS constraints
    (check-synth-next in SyGuS IF).
  - getAbductNext finds the next abduct for the current set of
    assertions and provided goal (get-abduct-next in SMT-LIB).
  - getInterpolantNext finds the next interpolant for the current set of
    assertions and provided goal (get-interpolant-next in SMT-LIB).

* *Pool-based Quantifier Instantiation*
  - declarePool declares symbol sets of terms called pools (declare-pool in
    SMT-LIB).
  - Pools can be used in annotations of quantified formulas for fine grained
    control over quantifier instantiations (:inst-pool, :inst-add-to-pool,
    :skolem-add-to-pool in SMT-LIB).

* Diagnostic Outputs
  - The option `-o TAG` can be used to enable a class of useful diagnostic
    information, such as the state of the input formula before and after
    pre-preprocessing, quantifier instantiations, literals learned
    during solving, among others. For SyGuS problems, it can be used to
    show candidate solutions and grammars that the solver has generated.

* *Unsat cores*
  - Production modes based on the new proof infrastructure
    (`--unsat-cores-mode=sat-proof`) and on the solving-under-assumption feature
    of Minisat (`--unsat-cores-mode=assumptions`). The mode based on SAT
    assumptions + preprocessing proofs is the new default.
  - Computing minimal unsat cores (option `--minimal-unsat-cores`).

* *Blocking Models*
  - TODO

* *Model Cores*
  - TODO

**Changes**

* CaDiCaL and SymFPU are now required dependencies.
* Options have been extensively refactored, please refer to the cvc5
  documentation for further information.
* Removed support for the CVC language.
* SyGuS: Removed support for SyGuS-IF 1.0.
* Removed support for the (non-standard) `define` command.
* Removed Java and Python bindings for the legacy API.
* Interactive shell: the GPL-licensed Readline library has been replaced the
  BSD-licensed Editline. Compiling with `--best` now enables Editline, instead
  of Readline. Without selecting optional GPL components, Editline-enabled CVC4
  builds will be BSD licensed.
* The semantics for division and remainder operators in the CVC language now
  correspond to SMT-LIB 2.6 semantics (i.e. a division by zero or a zero
  modulus results in a constant value, instead of an uninterpreted one). As a
  result the option `--bv-div-zero-const` has been removed. Similarly, when no
  language is set, the API semantics now correspond to the SMT-LIB 2.6
  semantics.
* The `competition` build type includes the dependencies used for SMT-COMP by
  default. Note that this makes this build type produce GPL-licensed binaries.
* Bit-vector operator bvxnor was previously mistakenly marked as
  left-assoicative in SMT-LIB. This has recently been corrected in SMT-LIB. We
  now restrict bvxnor to only allow two operands in order to avoid confusion
  about the semantics, since the behavior of n-ary operands to bvxnor is now
  undefined in SMT-LIB.
* SMT-LIB output for `get-model` command now conforms with the standard,
  and does *not* begin with the keyword `model`. The output
  is the same as before, only with this word removed from the beginning.
* Building with Python 2 is now deprecated.
* Removed support for redundant logics ALL_SUPPORTED and QF_ALL_SUPPORTED,
  use ALL and QF_ALL instead.
