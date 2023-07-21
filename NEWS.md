This file contains a summary of important user-visible changes.

**New Features**

- API: New API function
       `Solver::mkFloatingPoint(const Term& sign, const Term& exp, const Term& sig)`,
       returns a floating-point value from the three IEEE-754 bit-vector value
       components.
- API: Simplified the `Solver::mkTuple` method. The sorts of the elements no longer
       need to be provided.
- Support for timeout cores
  - API: New API function `Solver::getTimeoutCore()` when applicable
    returns a subset of the current assertions that cause the solver to timeout
    without a provided timeout (option `--timeout-core-timeout`).
  - SMT-LIB: New command `(get-timeout-core)` which invokes the above method.
- API: The option `--print-unsat-cores-full` has been renamed to
       `--print-cores-full`. Setting this option to true will print all
       assertions in the unsat core, regardless of whether they are named. This
       option also impacts how timeout cores are printed.
- API: Added support for querying the values of real algebraic numbers in the
       API. In particular, the methods `Term::isRealAlgebraicNumber()`,
       `Term::getRealAlgebraicNumberDefiningPolynomial()`,
       `Term::getRealAlgebraicNumberLowerBound()`, and
       `Term::getRealAlgebraicNumberUpperBound()` may now be used to query
       the contents of terms corresponding to real algebraic numbers.
- Removed support for the ANTLR parser and parsing for the TPTP language.
- API: Removed API support for the deprecated SyGuS 2.0 command
       `Solver::synthInv`. This method is equivalent to `Solver::synthFun`
       with a Boolean range sort.

cvc5 1.0.5
==========

- A new (hand-written) parser is available and enabled by default.
  - Note the previous parser can be enabled using command line options
    `--no-flex-parser --no-stdin-input-per-line`. These options will be
    available until version 1.1 is released.

cvc5 1.0.4
==========

**New Features**

- Support for the theory of (prime-order) finite fields:
  * Sorts are created with
    * C++: `Solver::makeFiniteFieldSort`
    * SMT-LIB: `(_ FiniteField P)` for prime order `P`
  * Constants are created with
    * C++: `Solver::makeFiniteFieldElem`
    * SMT-LIB: `(as ffN F)` for integer `N` and field sort `F`
  * The operators are multiplication, addition and negation
    * C++: kinds `FF_MUL`, `FF_ADD`, and `FF_NEG`
    * SMT-LIB: operators `ff.mul`, `ff.add`, and `ff.neg`
  * The only predicate is equality

cvc5 1.0.3
==========

**New Features**

- API: New API function `Solver::getVersion()`, returns a string representation
    of the solver version.
- Support for bit-vector overflow detection operators:
  * `BITVECTOR_UADDO` unsigned addition overflow detection
  * `BITVECTOR_SADDO` signed addition overflow detection
  * `BITVECTOR_UMULO` unsigned multiplication overflow detection
  * `BITVECTOR_SMULO` signed multiplication overflow detection
  * `BITVECTOR_USUBO` unsigned subtraction overflow detection
  * `BITVECTOR_SSUBO` signed subtraction overflow detection
  * `BITVECTOR_SDIVO` signed division overflow detection
- Support for Web Assembly compilation using Emscripten.

**Changes**

- The (non-standard) operators `BITVECTOR_TO_NAT` and `INT_TO_BITVECTOR` now
  belong to the UF theory. A logic that includes UF is required to use them.
- The sort for (non-standard) bit-vector operators `BITVECTOR_REDAND` and
  `BITVECTOR_REDOR` is now `(_ BitVec 1)` (was Boolean), following the
  definition of reduction operators in Verilog (their origin).
- Reenable functionality that allows `(get-model)` commands after answering
  `unknown` when `:produce-models` is set to `true`. Note that there is no
  guarantee that building a model succeeds in this case.

cvc5 1.0.2
==========

**Changes**

- API: Previously, it was not possible to share Sort, Term, Op, Grammar and
    datatype objects between Solver instances. This is now allowed for solvers
    that belong to the same thread.

cvc5 1.0.1
==========

**New Features**

- Support for cross-compiling an ARM binary of cvc5 on x86 macOS.
- Support for declaring oracle functions in the API via the method
  `declareOracleFun`. This allows users to declare functions whose semantics
  are associated with a provided executable implementation.

**Changes**

- Removed support for non-standard `declare-funs`, `declare-consts`, and
  `declare-sorts` commands.
- The kind for integer constants is now `CONST_INTEGER`, while real constants
  continue to have kind `CONST_RATIONAL`.
- Type rules for (dis)equality and if-then-else no longer allow mixing
  integers and reals. Type rules for other operators like `APPLY_UF` now
  require their arguments to match the type of the function being applied, and
  do not assume integer/real subtyping.
- The API method `mkTuple` no longer supports casting integers to reals when
  constructing tuples.

cvc5 1.0
=========

**Website**: https://cvc5.github.io

**Documentation**: https://cvc5.github.io/docs

**System Description**
  * *cvc5: A Versatile and Industrial-Strength SMT Solver.*  
    Barbosa H., Barrett C., Brain M., Kremer G., Lachnitt H.,
    Mann M., Mohamed A., Mohamed M., Niemetz A., Nötzli A.,
    Ozdemir A., Preiner M., Reynolds A., Sheng Y., Tinelli C., and Zohar Y.,
    TACAS 2022.

**New Features**

* *Streamlined C++ API*
  - Documentation: https://cvc5.github.io/docs/latest/api/cpp/cpp.html

* *Two new Python language bindings*
  - Base module: Feature complete with C++ API
  - Pythonic module: A pythonic wrapper around the base module
  - Documentation: https://cvc5.github.io/docs/latest/api/python/python.html

* *New Java language bindings*
  - Documentation: https://cvc5.github.io/docs/latest/api/java/java.html

* *Theory of Bags (Multisets)*
  - A new theory of bags, which are collections that allow duplicates. It
    supports basic operators like union disjoint, union max, intersection,
    difference subtract, difference remove, duplicate removal, and multiplicity
    of an element in a bag. 

* *Theory of Sequences*
  - A new parametric theory of sequences whose syntax is compatible with the
    syntax for sequences used by Z3.
  - A new array-inspired procedure (option `--seq-array`).

* *Arithmetic*
  - Nonlinear real arithmetic is now solved using a new solver based on
    cylindrical algebraic coverings. Includes full support for non-rational
    models and a number of options `--nl-cov-*` for, e.g., different projection
    operators, Lazard's lifting or variable elimination.
    The new solver requires the libpoly library, and Lazard's lifting
    additionally requires CoCoALib.

* *Arrays*
  - Added support for an `eqrange` predicate. `(eqrange a b i j)` is true
    if arrays `a` and `b` are equal on all indices within indices `i` and `j`.

* *Bit-vectors*
  - New bit-vector solver with CaDiCaL as default SAT back-end.
  - New approach for solving bit-vectors as integers (option `--solve-bv-as-int`).

* *Datatypes*
  - Support for generic datatype updaters `((_ update s) t u)` which replaces
    the field specified by selector `s` of `t` by the value `u`.

* *Integers*
  - Support for an integer operator `(_ iand n)` that returns the bitwise `and`
    of two integers, seen as integers modulo n.
  - Support for an integer operator `int.pow2`, used as `(int.pow2 x)` which
    represents 2 to the power of x.

* *Quantifiers*
  - Improved support for enumerative instantiation (option `--enum-inst`).
  - SyGuS-based quantifier instantiation (option `--sygus-inst`).

* *Strings*
  - Improved performance using new techniques, including model-based
    reductions, eager context-dependent simplification, and equality-based
    conflict finding.
  - Support for `str.indexof_re(s, r, n)`, which returns the index of the first
    occurrence of a regular expression `r` in a string `s` after index `n` or
    -1 if `r` does not match a substring after `n`.

* *Proofs*
  * Documentation available at:
    https://cvc5.github.io/docs/latest/proofs/proofs.html
  * When used after an unsatisfiable response to `checkSat`, `getProof`
    returns a representation of the refutation proof for the current set of
    assertions (get-proof in SMT-LIB).
  * Preliminary support for translations to external proof formats LFSC and Alethe.

* *Difficulty Estimation*
  - The API method `getDifficulty` returns a map from asserted formulas to
    integers which estimates how much that formula contributed to the
    difficulty of the overall problem (get-difficulty in SMT-LIB).

* *Learned Literals*
  - The API method `getLearnedLiterals` gets a list of literals that are
    entailed by the current set of assertions that were learned during solving
    (get-learned-literals in SMT-LIB).

* *Abduction and Interpolation*
  * The API method `getAbduct` can be used to find an abduct for the current set
    of assertions and provided goal (get-abduct in SMT-LIB). Optionally, a
    SyGuS grammar can be provided to restrict the shape of possible abducts.
    If using the text inferace, the grammar may be provided using the same
    syntax for grammars as in SyGuS IF format.
  * The API method `getInterpolant` can be used to find an interpolant for the
    current set of assertions and provided goal (get-interpolant in SMT-LIB).
    Like abduction, grammars may be provided to restrict the shape of
    interpolants.

* *Support for Incremental Synthesis Queries*
  - The core SyGuS solver now supports getting multiple solutions for a
    synthesis conjecture via the API. The method `checkSynthNext` finds the
    next SyGuS solution to the current set of SyGuS constraints
    (check-synth-next in SyGuS IF).
  - `getAbductNext` finds the next abduct for the current set of
    assertions and provided goal (get-abduct-next in SMT-LIB).
  - `getInterpolantNext` finds the next interpolant for the current set of
    assertions and provided goal (get-interpolant-next in SMT-LIB).

* *Pool-based Quantifier Instantiation*
  - The API method `declarePool` declares symbol sets of terms called pools
    (`declare-pool` in SMT-LIB).
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
    (`--unsat-cores-mode=sat-proof`) and on the solving-under-assumption
    feature of Minisat (`--unsat-cores-mode=assumptions`). The mode based on
    SAT assumptions + preprocessing proofs is the new default.
  - Computing minimal unsat cores (option `--minimal-unsat-cores`).

* *Blocking Models*
  - The API method `blockModels` can be used to block the current model using
    various policies for how to exclude the values of terms (`block-model` in
    SMT-LIB).
  - The API method `blockModelValues` can be used to block the current model
    for a provided set of terms (`block-model-values` in SMT-LIB).

* *Model Cores*
  - The API method `isModelCoreSymbol` can be used to query whether the value
    for a symbol was critical to whether the model satisfies the current set of
    assertions.
  - Models can be limited to show only model core symbols (option `--model-cores`).

**Changes**

* CaDiCaL and SymFPU are now required dependencies. CaDiCaL 1.4.1 is now the
  version used by default.
* Options have been extensively refactored, please refer to the cvc5
  documentation for further information.
* Removed support for the CVC language.
* SyGuS: Removed support for SyGuS-IF 1.0.
* Removed support for the (non-standard) `define` command.
* Removed the legacy API along with the Java and Python bindings for it.
* Interactive shell: the GPL-licensed Readline library has been replaced the
  BSD-licensed Editline. Compiling with `--best` now enables Editline, instead
  of Readline. Without selecting optional GPL components, Editline-enabled CVC4
  builds will be BSD licensed.
* The `competition` build type includes the dependencies used for SMT-COMP by
  default. Note that this makes this build type produce GPL-licensed binaries.
* Bit-vector operator `bvxnor` was previously mistakenly marked as
  left-assoicative in SMT-LIB. This has recently been corrected in SMT-LIB. We
  now restrict `bvxnor` to only allow two operands in order to avoid confusion
  about the semantics, since the behavior of n-ary operands to `bvxnor` is now
  undefined in SMT-LIB.
* SMT-LIB output for `get-model` command now conforms with the standard,
  and does *not* begin with the keyword `model`. The output
  is the same as before, only with this word removed from the beginning.
* Building with Python 2 is now deprecated.
* The SMT-LIB syntax for some extensions has been changed. Notably, set
  operators are now prefixed by `set.`, and relations by `rel.`. For example,
  `union` is now written `set.union`.
* Removed support for redundant logics `ALL_SUPPORTED` and `QF_ALL_SUPPORTED`,
  use `ALL` and `QF_ALL` instead.
