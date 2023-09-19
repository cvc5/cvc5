# FF Solver Architecture

The field solver implements the decision procedure from [OKTB23]:
["Satisfiability Modulo Finite
Fields"](https://doi.org/10.1007/978-3-031-37703-7_8), essentially
un-modified.

Here is a description of source files. When relevant, I give the part of
[OKTB23] that they implement:

* `theory_ff`: entry point to the theory, responsible for all finite-fields.
   Wraps a list of field-specific sub-theories and dispatches each fact to the
   relevant sub-theory.
   * For example, if a problem has elements of GF(3) and GF(5), there will be
      one sub-theory for each.
* `sub_theory`: [OKTB23]'s DecisionProcedure (Fig. 2)
* `core`: computes UNSAT cores; [OKTB23]'s IdealCalc (Fig. 4) and CoreFromTree (in Fig. 2)
* `multi_roots`: model contruction; [OKTB23]'s FindZero (Fig. 5) and ApplyRule (Fig. 6)
* `uni_roots`: univariate root-finding; [OKTB23]'s UnivariateZeros (in Fig. 6)
* `theory_ff_rewriter`: term rewriting for FF
* `theory_ff_type_rules`: term type-checking for FF
* `stats`: statistics
* `type_enumerator`: enumerating values in a field
