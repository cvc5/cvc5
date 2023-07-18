/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Gereon Kremer, Mudathir Mohamed
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Inference enumeration.
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__INFERENCE_ID_H
#define CVC5__THEORY__INFERENCE_ID_H

#include <iosfwd>

#include "expr/node.h"

namespace cvc5::internal {
namespace theory {

/** Types of inferences used in the procedure
 *
 * Note: The order in this enum matters in certain cases (e.g. inferences
 * related to normal forms in strings), where inferences that come first are
 * generally preferred.
 *
 * Notice that an inference is intentionally distinct from PfRule. An
 * inference captures *why* we performed a reasoning step, and a PfRule
 * rule captures *what* reasoning step was used. For instance, the inference
 * LEN_SPLIT translates to PfRule::SPLIT. The use of stats on inferences allows
 * us to know that we performed N splits (PfRule::SPLIT) because we wanted
 * to split on lengths for string equalities (Inference::LEN_SPLIT).
 */
enum class InferenceId
{
  // ---------------------------------- core
  // a conflict when two constants merge in the equality engine (of any theory)
  EQ_CONSTANT_MERGE,
  // a split from theory combination
  COMBINATION_SPLIT,
  // ---------------------------------- ext theory
  // a simplification from the extended theory utility
  EXTT_SIMPLIFY,
  // ---------------------------------- arith theory
  //-------------------- linear core
  // black box conflicts. It's magic.
  ARITH_BLACK_BOX,
  // conflicting equality
  ARITH_CONF_EQ,
  // conflicting lower bound
  ARITH_CONF_LOWER,
  // conflict due to trichotomy
  ARITH_CONF_TRICHOTOMY,
  // conflicting upper bound
  ARITH_CONF_UPPER,
  // conflict from simplex
  ARITH_CONF_SIMPLEX,
  // conflict from sum-of-infeasibility simplex
  ARITH_CONF_SOI_SIMPLEX,
  // conflict when getting constraint from fact queue
  ARITH_CONF_FACT_QUEUE,
  // conflict in tryBranchCut
  ARITH_CONF_BRANCH_CUT,
  // conflict in replayAssert
  ARITH_CONF_REPLAY_ASSERT,
  // conflict in replayLog
  ARITH_CONF_REPLAY_LOG,
  // conflict in replayLogRec
  ARITH_CONF_REPLAY_LOG_REC,
  // conflict from handleUnateProp
  ARITH_CONF_UNATE_PROP,
  // introduces split on a disequality
  ARITH_SPLIT_DEQ,
  // tighten integer inequalities to ceiling
  ARITH_TIGHTEN_CEIL,
  // tighten integer inequalities to floor
  ARITH_TIGHTEN_FLOOR,
  ARITH_APPROX_CUT,
  ARITH_BB_LEMMA,
  ARITH_DIO_CUT,
  ARITH_DIO_DECOMPOSITION,
  // unate lemma during presolve
  ARITH_UNATE,
  // row implication
  ARITH_ROW_IMPL,
  // a split that occurs when the non-linear solver changes values of arithmetic
  // variables in a model, but those variables are inconsistent with assignments
  // from another theory
  ARITH_SPLIT_FOR_NL_MODEL,
  // dummy lemma to demand a restart
  ARITH_DEMAND_RESTART,
  //-------------------- preprocessing
  // equivalence of term and its preprocessed form
  ARITH_PP_ELIM_OPERATORS,
  // a lemma from arithmetic preprocessing
  ARITH_PP_ELIM_OPERATORS_LEMMA,
  //-------------------- nonlinear core
  // simple congruence x=y => f(x)=f(y)
  ARITH_NL_CONGRUENCE,
  // shared term value split (for naive theory combination)
  ARITH_NL_SHARED_TERM_VALUE_SPLIT,
  // checkModel found a conflict with a quadratic equality
  ARITH_NL_CM_QUADRATIC_EQ,
  //-------------------- nonlinear incremental linearization solver
  // splitting on zero (NlSolver::checkSplitZero)
  ARITH_NL_SPLIT_ZERO,
  // based on sign (NlSolver::checkMonomialSign)
  ARITH_NL_SIGN,
  // based on comparing (abs) model values (NlSolver::checkMonomialMagnitude)
  ARITH_NL_COMPARISON,
  // based on inferring bounds (NlSolver::checkMonomialInferBounds)
  ARITH_NL_INFER_BOUNDS,
  // same as above, for inferences that introduce new terms
  ARITH_NL_INFER_BOUNDS_NT,
  // factoring (NlSolver::checkFactoring)
  ARITH_NL_FACTOR,
  // resolution bound inferences (NlSolver::checkMonomialInferResBounds)
  ARITH_NL_RES_INFER_BOUNDS,
  // tangent planes (NlSolver::checkTangentPlanes)
  ARITH_NL_TANGENT_PLANE,
  //-------------------- nonlinear transcendental solver
  // sine symmetry
  ARITH_NL_T_SINE_SYMM,
  // boundary reduction
  ARITH_NL_T_SINE_BOUNDARY_REDUCE,
  // purification of arguments to transcendental functions
  ARITH_NL_T_PURIFY_ARG,
  // purification of arguments to transcendental functions with phase shifting
  ARITH_NL_T_PURIFY_ARG_PHASE_SHIFT,
  // initial refinement (TranscendentalSolver::checkTranscendentalInitialRefine)
  ARITH_NL_T_INIT_REFINE,
  // pi bounds
  ARITH_NL_T_PI_BOUND,
  // monotonicity (TranscendentalSolver::checkTranscendentalMonotonic)
  ARITH_NL_T_MONOTONICITY,
  // tangent refinement (TranscendentalSolver::checkTranscendentalTangentPlanes)
  ARITH_NL_T_TANGENT,
  // secant refinement, the dual of the above inference
  ARITH_NL_T_SECANT,
  //-------------------- nonlinear iand solver
  // initial refinements (IAndSolver::checkInitialRefine)
  ARITH_NL_IAND_INIT_REFINE,
  // value refinements (IAndSolver::checkFullRefine)
  ARITH_NL_IAND_VALUE_REFINE,
  // sum refinements (IAndSolver::checkFullRefine)
  ARITH_NL_IAND_SUM_REFINE,
  // bitwise refinements (IAndSolver::checkFullRefine)
  ARITH_NL_IAND_BITWISE_REFINE,
  //-------------------- nonlinear pow2 solver
  // initial refinements (Pow2Solver::checkInitialRefine)
  ARITH_NL_POW2_INIT_REFINE,
  // value refinements (Pow2Solver::checkFullRefine)
  ARITH_NL_POW2_VALUE_REFINE,
  // monotonicity refinements (Pow2Solver::checkFullRefine)
  ARITH_NL_POW2_MONOTONE_REFINE,
  // trivial refinements (Pow2Solver::checkFullRefine)
  ARITH_NL_POW2_TRIVIAL_CASE_REFINE,
  //-------------------- nonlinear coverings solver
  // conflict / infeasible subset obtained from coverings
  ARITH_NL_COVERING_CONFLICT,
  // excludes an interval for a single variable
  ARITH_NL_COVERING_EXCLUDED_INTERVAL,
  //-------------------- nonlinear icp solver
  // conflict obtained from icp
  ARITH_NL_ICP_CONFLICT,
  // propagation / contraction of variable bounds from icp
  ARITH_NL_ICP_PROPAGATION,
  //-------------------- ff inference
  // ---------------------------------- end arith theory

  // ---------------------------------- finite field theory
  // a catch-all, for now
  FF_LEMMA,
  // ---------------------------------- end finite field theory

  // ---------------------------------- arrays theory
  ARRAYS_EXT,
  ARRAYS_READ_OVER_WRITE,
  ARRAYS_READ_OVER_WRITE_1,
  ARRAYS_READ_OVER_WRITE_CONTRA,
  // (= (select (as const (Array T1 T2) x) y) x)
  ARRAYS_CONST_ARRAY_DEFAULT,
  // an internally inferred tautological equality
  ARRAYS_EQ_TAUTOLOGY,
  // ---------------------------------- end arrays theory

  // ---------------------------------- bags theory
  BAGS_NON_NEGATIVE_COUNT,
  BAGS_BAG_MAKE,
  BAGS_BAG_MAKE_SPLIT,
  BAGS_SKOLEM,
  BAGS_EQUALITY,
  BAGS_DISEQUALITY,
  BAGS_CG_SPLIT,
  BAGS_EMPTY,
  BAGS_UNION_DISJOINT,
  BAGS_UNION_MAX,
  BAGS_INTERSECTION_MIN,
  BAGS_DIFFERENCE_SUBTRACT,
  BAGS_DIFFERENCE_REMOVE,
  BAGS_DUPLICATE_REMOVAL,
  BAGS_MAP_DOWN,
  BAGS_MAP_UP,
  BAGS_FILTER_DOWN,
  BAGS_FILTER_UP,
  BAGS_FOLD,
  BAGS_CARD,
  BAGS_CARD_EMPTY,
  TABLES_PRODUCT_UP,
  TABLES_PRODUCT_DOWN,
  TABLES_JOIN_UP,
  TABLES_JOIN_DOWN,
  TABLES_GROUP_NOT_EMPTY,
  TABLES_GROUP_UP1,
  TABLES_GROUP_UP2,
  TABLES_GROUP_DOWN,
  TABLES_GROUP_PART_COUNT,
  TABLES_GROUP_SAME_PROJECTION,
  TABLES_GROUP_SAME_PART,
  // ---------------------------------- end bags theory

  // ---------------------------------- bitvector theory
  BV_BITBLAST_CONFLICT,
  BV_BITBLAST_INTERNAL_EAGER_LEMMA,
  BV_BITBLAST_INTERNAL_BITBLAST_LEMMA,
  BV_LAYERED_CONFLICT,
  BV_LAYERED_LEMMA,
  BV_EXTF_LEMMA,
  BV_EXTF_COLLAPSE,
  // ---------------------------------- end bitvector theory

  // ---------------------------------- datatypes theory
  // (= k t) for fresh k
  DATATYPES_PURIFY,
  // (= (C t1 ... tn) (C s1 .. sn)) => (= ti si)
  DATATYPES_UNIF,
  // ((_ is Ci) t) => (= t (Ci (sel_1 t) ... (sel_n t)))
  DATATYPES_INST,
  // (or ((_ is C1) t) V ... V ((_ is Cn) t))
  DATATYPES_SPLIT,
  // (or ((_ is Ci) t) V (not ((_ is Ci) t)))
  DATATYPES_BINARY_SPLIT,
  // (not ((_ is C1) t)) ^ ... [j] ... ^ (not ((_ is Cn) t)) => ((_ is Cj) t)
  DATATYPES_LABEL_EXH,
  // (= t (Ci t1 ... tn)) => (= (sel_j t) rewrite((sel_j (Ci t1 ... tn))))
  DATATYPES_COLLAPSE_SEL,
  // (= (Ci t1...tn) (Cj t1...tn)) => false
  DATATYPES_CLASH_CONFLICT,
  // ((_ is Ci) t) ^ (= t (Cj t1 ... tn)) => false
  DATATYPES_TESTER_CONFLICT,
  // ((_ is Ci) t) ^ ((_ is Cj) s) ^ (= t s) => false
  DATATYPES_TESTER_MERGE_CONFLICT,
  // bisimilarity for codatatypes
  DATATYPES_BISIMILAR,
  // corecursive singleton equality
  DATATYPES_REC_SINGLETON_EQ,
  // corecursive singleton equality (not (= k1 k2)) for fresh k1, k2
  DATATYPES_REC_SINGLETON_FORCE_DEQ,
  // cycle conflict for datatypes
  DATATYPES_CYCLE,
  //-------------------- datatypes size/height
  // (>= (dt.size t) 0)
  DATATYPES_SIZE_POS,
  // (=> (= (dt.height t) 0) => (and (= (dt.height (sel_1 t)) 0) .... ))
  DATATYPES_HEIGHT_ZERO,
  //-------------------- sygus extension
  // a sygus symmetry breaking lemma (or ~is-C1( t1 ) V ... V ~is-Cn( tn ) )
  // where t1 ... tn are unique shared selector chains. For details see
  // Reynolds et al CAV 2019
  DATATYPES_SYGUS_SYM_BREAK,
  // a conjecture-dependent symmetry breaking lemma, which may be used to
  // exclude constructors for variables that irrelevant for a synthesis
  // conjecture
  DATATYPES_SYGUS_CDEP_SYM_BREAK,
  // an enumerator-specific symmetry breaking lemma, which are used e.g. for
  // excluding certain kinds of constructors
  DATATYPES_SYGUS_ENUM_SYM_BREAK,
  // a simple static symmetry breaking lemma (see Reynolds et al CAV 2019)
  DATATYPES_SYGUS_SIMPLE_SYM_BREAK,
  // (dt.size t) <= N, to implement fair enumeration when sygus-fair=dt-size
  DATATYPES_SYGUS_FAIR_SIZE,
  // (dt.size t) <= N => (or ~is-C1( t1 ) V ... V ~is-Cn( tn ) ) if using
  // sygus-fair=direct
  DATATYPES_SYGUS_FAIR_SIZE_CONFLICT,
  // used for implementing variable agnostic enumeration
  DATATYPES_SYGUS_VAR_AGNOSTIC,
  // handles case the model value for a sygus term violates the size bound
  DATATYPES_SYGUS_SIZE_CORRECTION,
  // handles case the model value for a sygus term does not exist
  DATATYPES_SYGUS_VALUE_CORRECTION,
  // s <= (dt.size t), where s is a term that must be less than the current
  // size bound based on our fairness strategy. For instance, s may be
  // (dt.size e) for (each) enumerator e when multiple enumerators are present.
  DATATYPES_SYGUS_MT_BOUND,
  // (dt.size t) >= 0
  DATATYPES_SYGUS_MT_POS,
  // ---------------------------------- end datatypes theory

  //-------------------------------------- floating point theory
  // a lemma sent during TheoryFp::ppRewrite
  FP_PREPROCESS,
  // a lemma sent during TheoryFp::convertAndEquateTerm
  FP_EQUATE_TERM,
  // a lemma sent during TheoryFp::registerTerm
  FP_REGISTER_TERM,
  //-------------------------------------- end floating point theory

  //-------------------------------------- quantifiers theory
  //-------------------- types of instantiations.
  // Notice the identifiers in this section cover all the techniques used for
  // quantifier instantiation. The subcategories below are for specific lemmas
  // that are not instantiation lemmas added, per technique.
  // instantiation from E-matching
  QUANTIFIERS_INST_E_MATCHING,
  // E-matching using simple trigger implementation
  QUANTIFIERS_INST_E_MATCHING_SIMPLE,
  // E-matching using multi-triggers
  QUANTIFIERS_INST_E_MATCHING_MT,
  // E-matching using linear implementation of multi-triggers
  QUANTIFIERS_INST_E_MATCHING_MTL,
  // instantiation due to higher-order matching on top of e-matching
  QUANTIFIERS_INST_E_MATCHING_HO,
  // E-matching based on variable triggers
  QUANTIFIERS_INST_E_MATCHING_VAR_GEN,
  // E-matching based on relational triggers
  QUANTIFIERS_INST_E_MATCHING_RELATIONAL,
  // conflicting instantiation from conflict-based instantiation
  QUANTIFIERS_INST_CBQI_CONFLICT,
  // propagating instantiation from conflict-based instantiation
  QUANTIFIERS_INST_CBQI_PROP,
  // instantiation from naive exhaustive instantiation in finite model finding
  QUANTIFIERS_INST_FMF_EXH,
  // instantiation from finite model finding based on its model-based algorithm
  QUANTIFIERS_INST_FMF_FMC,
  // instantiation from running exhaustive instantiation on a subdomain of
  // the quantified formula in finite model finding based on its model-based
  // algorithm
  QUANTIFIERS_INST_FMF_FMC_EXH,
  // instantiations from counterexample-guided instantiation
  QUANTIFIERS_INST_CEGQI,
  // instantiations from syntax-guided instantiation
  QUANTIFIERS_INST_SYQI,
  // instantiations from model-based instantiation
  QUANTIFIERS_INST_MBQI,
  // instantiations from enumerative instantiation
  QUANTIFIERS_INST_ENUM,
  // instantiations from pool instantiation
  QUANTIFIERS_INST_POOL,
  // instantiations from pool instantiation (tuple semantics)
  QUANTIFIERS_INST_POOL_TUPLE,
  //-------------------- bounded integers
  // a proxy lemma from bounded integers, used to control bounds on ground terms
  QUANTIFIERS_BINT_PROXY,
  // a proxy lemma to minimize an instantiation of non-ground terms
  QUANTIFIERS_BINT_MIN_NG,
  //-------------------- counterexample-guided instantiation
  // a counterexample lemma
  QUANTIFIERS_CEGQI_CEX,
  // an auxiliary lemma from counterexample lemma
  QUANTIFIERS_CEGQI_CEX_AUX,
  // a reduction lemma for nested quantifier elimination
  QUANTIFIERS_CEGQI_NESTED_QE,
  // G2 => G1 where G2 is a counterexample literal for a nested quantifier whose
  // counterexample literal is G1.
  QUANTIFIERS_CEGQI_CEX_DEP,
  // 0 < delta
  QUANTIFIERS_CEGQI_VTS_LB_DELTA,
  // delta < c, for positive c
  QUANTIFIERS_CEGQI_VTS_UB_DELTA,
  // infinity > c
  QUANTIFIERS_CEGQI_VTS_LB_INF,
  //-------------------- oracles
  // A lemma generated by an oracle interface quantified formula.
  // For example, (= (f c) d) where (c, d) is an I/O pair obtained from calling
  // the oracle associated with oracle function f.
  QUANTIFIERS_ORACLE_INTERFACE,
  // purification lemma to ensure oracle functions in substitutions are taken
  // into account
  QUANTIFIERS_ORACLE_PURIFY_SUBS,
  //-------------------- syntax-guided instantiation
  // a counterexample lemma
  QUANTIFIERS_SYQI_CEX,
  // evaluation unfolding for syntax-guided instantiation
  QUANTIFIERS_SYQI_EVAL_UNFOLD,
  //-------------------- sygus solver
  // G or ~G where G is the active guard for a sygus enumerator
  QUANTIFIERS_SYGUS_ENUM_ACTIVE_GUARD_SPLIT,
  // manual exclusion of a current solution for an actively generated enumerator
  QUANTIFIERS_SYGUS_ACTIVE_GEN_EXCLUDE_CURRENT,
  // manual exclusion of a current solution for sygus-stream
  QUANTIFIERS_SYGUS_STREAM_EXCLUDE_CURRENT,
  // manual exclusion of a current solution for incremental sygus
  QUANTIFIERS_SYGUS_INC_EXCLUDE_CURRENT,
  // manual exclusion of a current solution for a failed side condition
  QUANTIFIERS_SYGUS_SC_EXCLUDE_CURRENT,
  // manual exclusion of a current solution for a failed verification
  QUANTIFIERS_SYGUS_NO_VERIFY_EXCLUDE_CURRENT,
  // manual exclusion of a current solution for a repeated counterexample
  QUANTIFIERS_SYGUS_REPEAT_CEX_EXCLUDE_CURRENT,
  // ~Q where Q is a PBE conjecture with conflicting examples
  QUANTIFIERS_SYGUS_EXAMPLE_INFER_CONTRA,
  // infeasible determined by single-invocation solver
  QUANTIFIERS_SYGUS_SI_INFEASIBLE,
  // unif+pi symmetry breaking between multiple enumerators
  QUANTIFIERS_SYGUS_UNIF_PI_INTER_ENUM_SB,
  // unif+pi separation lemma
  QUANTIFIERS_SYGUS_UNIF_PI_SEPARATION,
  // unif+pi lemma for fairness of size of enumerators
  QUANTIFIERS_SYGUS_UNIF_PI_FAIR_SIZE,
  // unif+pi lemma for removing redundant operators
  QUANTIFIERS_SYGUS_UNIF_PI_REM_OPS,
  // symmetry breaking for enumerators
  QUANTIFIERS_SYGUS_UNIF_PI_ENUM_SB,
  // constraining terms to be in the domain of output
  QUANTIFIERS_SYGUS_UNIF_PI_DOMAIN,
  // condition exclusion from sygus unif
  QUANTIFIERS_SYGUS_UNIF_PI_COND_EXCLUDE,
  // refinement lemma from sygus unif
  QUANTIFIERS_SYGUS_UNIF_PI_REFINEMENT,
  // symmetry breaking lemma from unsat core learning algorithm initialization
  QUANTIFIERS_SYGUS_CEGIS_UCL_SYM_BREAK,
  // candidate exclusion lemma from unsat core learning algorithm
  QUANTIFIERS_SYGUS_CEGIS_UCL_EXCLUDE,
  // candidate exclusion lemma from repair constants algorithm
  QUANTIFIERS_SYGUS_REPAIR_CONST_EXCLUDE,
  // a counterexample-guided inductive synthesis refinement lemma
  QUANTIFIERS_SYGUS_CEGIS_REFINE,
  // a cegis refinement lemma found by sampling
  QUANTIFIERS_SYGUS_CEGIS_REFINE_SAMPLE,
  // a lemma based on refinement lemma evaluation
  QUANTIFIERS_SYGUS_REFINE_EVAL,
  // an evaluation unfolding lemma
  QUANTIFIERS_SYGUS_EVAL_UNFOLD,
  // candidate exclusion lemma from programming-by-examples
  QUANTIFIERS_SYGUS_PBE_EXCLUDE,
  // a lemma generated while constructing a candidate solution for PBE
  QUANTIFIERS_SYGUS_PBE_CONSTRUCT_SOL,
  // complete enumeration lemma
  QUANTIFIERS_SYGUS_COMPLETE_ENUM,
  // infeasible due to side condition (e.g. for abduction)
  QUANTIFIERS_SYGUS_SC_INFEASIBLE,
  //-------------------- dynamic splitting
  // a dynamic split from quantifiers
  QUANTIFIERS_DSPLIT,
  //-------------------- induction / conjecture generation
  // a split on a conjecture for inductive theorem proving
  QUANTIFIERS_CONJ_GEN_SPLIT,
  // enumeration of ground terms for inductive theorem proving
  QUANTIFIERS_CONJ_GEN_GT_ENUM,
  //-------------------- miscellaneous
  // skolemization
  QUANTIFIERS_SKOLEMIZE,
  // Q1 <=> Q2, where Q1 and Q2 are alpha equivalent
  QUANTIFIERS_REDUCE_ALPHA_EQ,
  // a higher-order match predicate lemma
  QUANTIFIERS_HO_MATCH_PRED,
  // purification of non-variable higher-order function
  QUANTIFIERS_HO_PURIFY,
  // reduction of quantifiers that don't have triggers that cover all variables
  QUANTIFIERS_PARTIAL_TRIGGER_REDUCE,
  // a purification lemma for a ground term appearing in a quantified formula,
  // used to ensure E-matching has equality information for that term
  QUANTIFIERS_GT_PURIFY,
  // when term indexing discovers disequal congruent terms in the master
  // equality engine
  QUANTIFIERS_TDB_DEQ_CONG,
  //-------------------------------------- end quantifiers theory

  // ---------------------------------- sep theory
  // ensures that pto is a function: (pto x y) ^ ~(pto z w) ^ x = z => y != w
  SEP_PTO_NEG_PROP,
  // enforces injectiveness of pto: (pto x y) ^ (pto y w) ^ x = y => y = w
  SEP_PTO_PROP,
  // introduces a label for a heap, of the form U => L, where U is an
  // unlabelled separation logic predicate and L is its labelled form
  SEP_LABEL_INTRO,
  // introduces the set constraints for a label
  SEP_LABEL_DEF,
  // lemma for sep.emp
  SEP_EMP,
  // positive reduction for sep constraint
  SEP_POS_REDUCTION,
  // negative reduction for sep constraint
  SEP_NEG_REDUCTION,
  // model-based refinement for negated star/wand
  SEP_REFINEMENT,
  // sep.nil is not in the heap
  SEP_NIL_NOT_IN_HEAP,
  // a symmetry breaking lemma
  SEP_SYM_BREAK,
  // finite witness data lemma
  SEP_WITNESS_FINITE_DATA,
  // element distinctness lemma
  SEP_DISTINCT_REF,
  // reference bound lemma
  SEP_REF_BOUND,
  // ---------------------------------- end sep theory

  // ---------------------------------- sets theory
  //-------------------- sets core solver
  // split when computing care graph
  SETS_SKOLEM,
  SETS_CG_SPLIT,
  SETS_COMPREHENSION,
  SETS_DEQ,
  SETS_DOWN_CLOSURE,
  // conflict when two singleton/emptyset terms merge
  SETS_EQ_CONFLICT,
  SETS_EQ_MEM,
  SETS_EQ_MEM_CONFLICT,
  SETS_FILTER_DOWN,
  SETS_FILTER_UP,
  SETS_FOLD,
  SETS_MAP_DOWN_POSITIVE,
  SETS_MAP_UP,
  SETS_MEM_EQ,
  SETS_MEM_EQ_CONFLICT,
  SETS_PROXY,
  SETS_PROXY_SINGLETON,
  SETS_SINGLETON_EQ,
  SETS_UP_CLOSURE,
  SETS_UP_CLOSURE_2,
  SETS_UP_UNIV,
  //-------------------- sets cardinality solver
  // split on emptyset
  SETS_CARD_SPLIT_EMPTY,
  // split on equality between two distinct Venn regions
  SETS_CARD_SPLIT_EQ,
  // cycle of cardinalities, hence all sets have the same
  SETS_CARD_CYCLE,
  // two sets have the same cardinality
  SETS_CARD_EQUAL,
  SETS_CARD_GRAPH_EMP,
  SETS_CARD_GRAPH_EMP_PARENT,
  SETS_CARD_GRAPH_EQ_PARENT,
  SETS_CARD_GRAPH_EQ_PARENT_2,
  SETS_CARD_GRAPH_PARENT_SINGLETON,
  // cardinality is at least the number of elements we already know
  SETS_CARD_MINIMAL,
  // negative members are part of the universe
  SETS_CARD_NEGATIVE_MEMBER,
  // all sets have non-negative cardinality
  SETS_CARD_POSITIVE,
  // the universe is a superset of every set
  SETS_CARD_UNIV_SUPERSET,
  // cardinality of the universe is at most cardinality of the type
  SETS_CARD_UNIV_TYPE,
  //-------------------- sets relations solver
  SETS_RELS_IDENTITY_DOWN,
  SETS_RELS_IDENTITY_UP,
  SETS_RELS_JOIN_COMPOSE,
  SETS_RELS_JOIN_IMAGE_DOWN,
  SETS_RELS_JOIN_IMAGE_UP,
  SETS_RELS_JOIN_SPLIT_1,
  SETS_RELS_JOIN_SPLIT_2,
  SETS_RELS_PRODUCE_COMPOSE,
  SETS_RELS_PRODUCT_SPLIT,
  SETS_RELS_TCLOSURE_FWD,
  SETS_RELS_TCLOSURE_UP,
  SETS_RELS_TRANSPOSE_EQ,
  SETS_RELS_TRANSPOSE_REV,
  SETS_RELS_TUPLE_REDUCTION,
  SETS_RELS_GROUP_NOT_EMPTY,
  SETS_RELS_GROUP_UP1,
  SETS_RELS_GROUP_UP2,
  SETS_RELS_GROUP_DOWN,
  SETS_RELS_GROUP_PART_MEMBER,
  SETS_RELS_GROUP_SAME_PROJECTION,
  SETS_RELS_GROUP_SAME_PART,
  //-------------------------------------- end sets theory

  //-------------------------------------- strings theory
  //-------------------- base solver
  // initial normalize singular
  //   x1 = "" ^ ... ^ x_{i-1} = "" ^ x_{i+1} = "" ^ ... ^ xn = "" =>
  //   x1 ++ ... ++ xn = xi
  STRINGS_I_NORM_S,
  // initial constant merge
  //   explain_constant(x, c) => x = c
  // Above, explain_constant(x,c) is a basic explanation of why x must be equal
  // to string constant c, which is computed by taking arguments of
  // concatenation terms that are entailed to be constants. For example:
  //  ( y = "AB" ^ z = "C" ) => y ++ z = "ABC"
  STRINGS_I_CONST_MERGE,
  // initial constant conflict
  //    ( explain_constant(x, c1) ^ explain_constant(x, c2) ^ x = y) => false
  // where c1 != c2.
  STRINGS_I_CONST_CONFLICT,
  // initial normalize
  // Given two concatenation terms, this is applied when we find that they are
  // equal after e.g. removing strings that are currently empty. For example:
  //   y = "" ^ z = "" => x ++ y = z ++ x
  STRINGS_I_NORM,
  // split between the argument of two equated str.unit terms
  STRINGS_UNIT_SPLIT,
  // a code point must be out of bounds due to (str.unit x) = (str.unit y) and
  // x != y.
  STRINGS_UNIT_INJ_OOB,
  // injectivity of seq.unit
  // (seq.unit x) = (seq.unit y) => x=y, or
  // (seq.unit x) = (seq.unit c) => x=c
  STRINGS_UNIT_INJ,
  // unit constant conflict
  // (seq.unit x) = C => false if |C| != 1.
  STRINGS_UNIT_CONST_CONFLICT,
  // injectivity of seq.unit for disequality
  // (seq.unit x) != (seq.unit y) => x != y, or
  // (seq.unit x) != (seq.unit c) => x != c
  STRINGS_UNIT_INJ_DEQ,
  // A split due to cardinality
  STRINGS_CARD_SP,
  // The cardinality inference for strings, see Liang et al CAV 2014.
  STRINGS_CARDINALITY,
  //-------------------- core solver
  // A cycle in the empty string equivalence class, e.g.:
  //   x ++ y = "" => x = ""
  // This is typically not applied due to length constraints implying emptiness.
  STRINGS_I_CYCLE_E,
  // A cycle in the containment ordering.
  //   x = y ++ x => y = "" or
  //   x = y ++ z ^ y = x ++ w => z = "" ^ w = ""
  // This is typically not applied due to length constraints implying emptiness.
  STRINGS_I_CYCLE,
  // Flat form constant
  //   x = y ^ x = z ++ c ... ^ y = z ++ d => false
  // where c and d are distinct constants.
  STRINGS_F_CONST,
  // Flat form unify
  //   x = y ^ x = z ++ x' ... ^ y = z ++ y' ^ len(x') = len(y') => x' = y'
  // Notice flat form instances are similar to normal form inferences but do
  // not involve recursive explanations.
  STRINGS_F_UNIFY,
  // Flat form endpoint empty
  //   x = y ^ x = z ^ y = z ++ y' => y' = ""
  STRINGS_F_ENDPOINT_EMP,
  // Flat form endpoint equal
  //   x = y ^ x = z ++ x' ^ y = z ++ y' => x' = y'
  STRINGS_F_ENDPOINT_EQ,
  // Flat form not contained
  // x = c ^ x = y => false when rewrite( contains( y, c ) ) = false
  STRINGS_F_NCTN,
  // Normal form equality conflict
  //   x = N[x] ^ y = N[y] ^ x=y => false
  // where Rewriter::rewrite(N[x]=N[y]) = false.
  STRINGS_N_EQ_CONF,
  // Given two normal forms, infers that the remainder one of them has to be
  // empty. For example:
  //    If x1 ++ x2 = y1 and x1 = y1, then x2 = ""
  STRINGS_N_ENDPOINT_EMP,
  // Given two normal forms, infers that two components have to be the same if
  // they have the same length. For example:
  //   If x1 ++ x2 = x3 ++ x4 and len(x1) = len(x3) then x1 = x3
  STRINGS_N_UNIFY,
  // Given two normal forms, infers that the endpoints have to be the same. For
  // example:
  //   If x1 ++ x2 = x3 ++ x4 ++ x5 and x1 = x3 then x2 = x4 ++ x5
  STRINGS_N_ENDPOINT_EQ,
  // Given two normal forms with constant endpoints, infers a conflict if the
  // endpoints do not agree. For example:
  //   If "abc" ++ ... = "bc" ++ ... then conflict
  STRINGS_N_CONST,
  // infer empty, for example:
  //     (~) x = ""
  // This is inferred when we encounter an x such that x = "" rewrites to a
  // constant. This inference is used for instance when we otherwise would have
  // split on the emptiness of x but the rewriter tells us the emptiness of x
  // can be inferred.
  STRINGS_INFER_EMP,
  // string split constant propagation, for example:
  //     x = y, x = "abc", y = y1 ++ "b" ++ y2
  //       implies y1 = "a" ++ y1'
  STRINGS_SSPLIT_CST_PROP,
  // string split variable propagation, for example:
  //     x = y, x = x1 ++ x2, y = y1 ++ y2, len( x1 ) >= len( y1 )
  //       implies x1 = y1 ++ x1'
  // This is inspired by Zheng et al CAV 2015.
  STRINGS_SSPLIT_VAR_PROP,
  // length split, for example:
  //     len( x1 ) = len( y1 ) V len( x1 ) != len( y1 )
  // This is inferred when e.g. x = y, x = x1 ++ x2, y = y1 ++ y2.
  STRINGS_LEN_SPLIT,
  // length split empty, for example:
  //     z = "" V z != ""
  // This is inferred when, e.g. x = y, x = z ++ x1, y = y1 ++ z
  STRINGS_LEN_SPLIT_EMP,
  // string split constant
  //    x = y, x = "c" ++ x2, y = y1 ++ y2, y1 != ""
  //      implies y1 = "c" ++ y1'
  // This is a special case of F-Split in Figure 5 of Liang et al CAV 2014.
  STRINGS_SSPLIT_CST,
  // string split variable, for example:
  //    x = y, x = x1 ++ x2, y = y1 ++ y2
  //      implies x1 = y1 ++ x1' V y1 = x1 ++ y1'
  // This is rule F-Split in Figure 5 of Liang et al CAV 2014.
  STRINGS_SSPLIT_VAR,
  // flat form loop, for example:
  //    x = y, x = x1 ++ z, y = z ++ y2
  //      implies z = u2 ++ u1, u in ( u1 ++ u2 )*, x1 = u2 ++ u, y2 = u ++ u1
  //        for fresh u, u1, u2.
  // This is the rule F-Loop from Figure 5 of Liang et al CAV 2014.
  STRINGS_FLOOP,
  // loop conflict ???
  STRINGS_FLOOP_CONFLICT,
  // Normal form inference
  // x = y ^ z = y => x = z
  // This is applied when y is the normal form of both x and z.
  STRINGS_NORMAL_FORM,
  // Normal form not contained, same as FFROM_NCTN but for normal forms
  STRINGS_N_NCTN,
  // Length normalization
  //   x = y => len( x ) = len( y )
  // Typically applied when y is the normal form of x.
  STRINGS_LEN_NORM,
  // When x ++ x' ++ ... != "abc" ++ y' ++ ... ^ len(x) != len(y), we apply the
  // inference:
  //   x = "" v x != ""
  STRINGS_DEQ_DISL_EMP_SPLIT,
  // When x ++ x' ++ ... != "abc" ++ y' ++ ... ^ len(x) = 1, we apply the
  // inference:
  //   x = "a" v x != "a"
  STRINGS_DEQ_DISL_FIRST_CHAR_EQ_SPLIT,
  // When x ++ x' ++ ... != "abc" ++ y' ++ ... ^ len(x) != "", we apply the
  // inference:
  //   ni = x ++ x' ++ ... ^ nj = "abc" ++ y' ++ ... ^ x != "" --->
  //     x = k1 ++ k2 ^ len(k1) = 1 ^ (k1 != "a" v x = "a" ++  k2)
  STRINGS_DEQ_DISL_FIRST_CHAR_STRING_SPLIT,
  // When x ++ x' ++ ... != y ++ y' ++ ... ^ len(x) != len(y), we apply the
  // inference:
  //   ni = x ++ x' ++ ... ^ nj = y ++ y' ++ ... ^ ni != nj ^ len(x) != len(y)
  //     --->
  //       len(k1) = len(x) ^ len(k2) = len(y) ^ (y = k1 ++ k3 v x = k1 ++ k2)
  STRINGS_DEQ_DISL_STRINGS_SPLIT,
  // When x ++ x' ++ ... != y ++ y' ++ ... ^ len(x) = len(y), we apply the
  // inference:
  //   x = y v x != y
  STRINGS_DEQ_STRINGS_EQ,
  // When x ++ x' ++ ... != y ++ y' ++ ... and we do not know how the lengths
  // of x and y compare, we apply the inference:
  //   len(x) = len(y) v len(x) != len(y)
  STRINGS_DEQ_LENS_EQ,
  // When px ++ x ++ ... != py ^ len(px ++ x ++ ...) = len(py), we apply the
  // following inference that infers that the remainder of the longer normal
  // form must be empty:
  //   ni = px ++ x ++ ... ^ nj = py ^ len(ni) = len(nj) --->
  //     x = "" ^ ...
  STRINGS_DEQ_NORM_EMP,
  // When two strings are disequal s != t and the comparison of their lengths
  // is unknown, we apply the inference:
  //   len(s) != len(t) V len(s) = len(t)
  STRINGS_DEQ_LENGTH_SP,
  // Disequality extensionality
  // x != y => ( seq.len(x) != seq.len(y) or
  //             ( seq.nth(x, d) != seq.nth(y, d) ^ 0 <= d < seq.len(x) ) )
  STRINGS_DEQ_EXTENSIONALITY,
  //-------------------- codes solver
  // str.to_code( v ) = rewrite( str.to_code(c) )
  // where v is the proxy variable for c.
  STRINGS_CODE_PROXY,
  // str.code(x) = -1 V str.code(x) != str.code(y) V x = y
  STRINGS_CODE_INJ,
  //-------------------- sequence update solver
  // update over unit
  STRINGS_ARRAY_UPDATE_UNIT,
  // update over conatenation
  STRINGS_ARRAY_UPDATE_CONCAT,
  // update over conatenation, inverse
  STRINGS_ARRAY_UPDATE_CONCAT_INVERSE,
  // nth over unit
  STRINGS_ARRAY_NTH_UNIT,
  // nth over conatenation
  STRINGS_ARRAY_NTH_CONCAT,
  // nth over extract
  STRINGS_ARRAY_NTH_EXTRACT,
  // nth over update
  STRINGS_ARRAY_NTH_UPDATE,
  // reasoning about the nth term from update term
  STRINGS_ARRAY_NTH_TERM_FROM_UPDATE,
  // reasoning about whether an update changes a term or not
  STRINGS_ARRAY_UPDATE_BOUND,
  // splitting about equality of sequences
  STRINGS_ARRAY_EQ_SPLIT,
  // nth over update when updated with an unit term
  STRINGS_ARRAY_NTH_UPDATE_WITH_UNIT,
  // nth over reverse
  STRINGS_ARRAY_NTH_REV,
  //-------------------- regexp solver
  // regular expression normal form conflict
  //   ( x in R ^ x = y ^ rewrite((str.in_re y R)) = false ) => false
  // where y is the normal form computed for x.
  STRINGS_RE_NF_CONFLICT,
  // regular expression unfolding
  // This is a general class of inferences of the form:
  //   (x in R) => F
  // where F is formula expressing the next step of checking whether x is in
  // R.  For example:
  //   (x in (R)*) =>
  //   x = "" V x in R V ( x = x1 ++ x2 ++ x3 ^ x1 in R ^ x2 in (R)* ^ x3 in R)
  STRINGS_RE_UNFOLD_POS,
  // Same as above, for negative memberships
  STRINGS_RE_UNFOLD_NEG,
  // intersection inclusion conflict
  //   (x in R1 ^ ~ x in R2) => false  where [[includes(R2,R1)]]
  // Where includes(R2,R1) is a heuristic check for whether R2 includes R1.
  STRINGS_RE_INTER_INCLUDE,
  // intersection conflict, using regexp intersection computation
  //   (x in R1 ^ x in R2) => false   where [[intersect(R1, R2) = empty]]
  STRINGS_RE_INTER_CONF,
  // intersection inference
  //   (x in R1 ^ y in R2 ^ x = y) => (x in re.inter(R1,R2))
  STRINGS_RE_INTER_INFER,
  // regular expression delta
  //   (x = "" ^ x in R) => C
  // where "" in R holds if and only if C holds.
  STRINGS_RE_DELTA,
  // regular expression delta conflict
  //   (x = "" ^ x in R) => false
  // where R does not accept the empty string.
  STRINGS_RE_DELTA_CONF,
  // regular expression derive ???
  STRINGS_RE_DERIVE,
  //-------------------- extended function solver
  // Standard extended function inferences from context-dependent rewriting
  // produced by constant substitutions. See Reynolds et al CAV 2017. These are
  // inferences of the form:
  //   X = Y => f(X) = t   when   rewrite( f(Y) ) = t
  // where X = Y is a vector of equalities, where some of Y may be constants.
  STRINGS_EXTF,
  // Same as above, for normal form substitutions.
  STRINGS_EXTF_N,
  // Decompositions based on extended function inferences from context-dependent
  // rewriting produced by constant substitutions. This is like the above, but
  // handles cases where the inferred predicate is not necessarily an equality
  // involving f(X). For example:
  //   x = "A" ^ contains( y ++ x, "B" ) => contains( y, "B" )
  // This is generally only inferred if contains( y, "B" ) is a known term in
  // the current context.
  STRINGS_EXTF_D,
  // Same as above, for normal form substitutions.
  STRINGS_EXTF_D_N,
  // Extended function equality rewrite. This is an inference of the form:
  //   t = s => P
  // where P is a predicate implied by rewrite( t = s ).
  // Typically, t is an application of an extended function and s is a constant.
  // It is generally only inferred if P is a predicate over known terms.
  STRINGS_EXTF_EQ_REW,
  // contain transitive
  //   ( str.contains( s, t ) ^ ~contains( s, r ) ) => ~contains( t, r ).
  STRINGS_CTN_TRANS,
  // contain decompose
  //  str.contains( x, str.++( y1, ..., yn ) ) => str.contains( x, yi ) or
  //  ~str.contains( str.++( x1, ..., xn ), y ) => ~str.contains( xi, y )
  STRINGS_CTN_DECOMPOSE,
  // contain neg equal
  //   ( len( x ) = len( s ) ^ ~contains( x, s ) ) => x != s
  STRINGS_CTN_NEG_EQUAL,
  // contain positive
  //   str.contains( x, y ) => x = w1 ++ y ++ w2
  // where w1 and w2 are skolem variables.
  STRINGS_CTN_POS,
  // All reduction inferences of the form:
  //   f(x1, .., xn) = y ^ P(x1, ..., xn, y)
  // where f is an extended function, y is the purification variable for
  // f(x1, .., xn) and P is the reduction predicate for f
  // (see theory_strings_preprocess).
  STRINGS_REDUCTION,
  //-------------------- merge conflicts
  // prefix conflict
  STRINGS_PREFIX_CONFLICT,
  // minimized prefix conflict
  STRINGS_PREFIX_CONFLICT_MIN,
  // arithmetic bound conflict
  STRINGS_ARITH_BOUND_CONFLICT,
  //-------------------- other
  // a lemma added during term registration for an atomic term
  STRINGS_REGISTER_TERM_ATOMIC,
  // a lemma added during term registration
  STRINGS_REGISTER_TERM,
  // a split during collect model info
  STRINGS_CMI_SPLIT,
  //-------------------------------------- end strings theory

  //-------------------------------------- uf theory
  // Clause from the uf symmetry breaker
  UF_BREAK_SYMMETRY,
  //-------------------- cardinality extension to UF
  // The inferences below are described in Reynolds' thesis 2013.
  // conflict of the form (card_T n) => (not (distinct t1 ... tn))
  UF_CARD_CLIQUE,
  // conflict of the form (not (card_T1 n1)) ^ ... (not (card_Tk nk)) ^ (card n)
  // where n1 + ... + nk >= n, where (card n) is a combined cardinality
  // constraint.
  UF_CARD_COMBINED,
  // (not (card_T n)) => (distinct t1 ... tn)
  UF_CARD_ENFORCE_NEGATIVE,
  // used to make the index terms in cardinality constraints equal
  UF_CARD_EQUIV,
  // conflict of the form (not (card_T1 n)) ^ (card_T2 m) where the cardinality
  // of T2 can be assumed to be without loss of generality larger than T1 due to
  // monotonicity reasoning (Claessen et al 2011).
  UF_CARD_MONOTONE_COMBINED,
  // conflict of the form (not (card_T n)) ^ (card_T m) where n>m
  UF_CARD_SIMPLE_CONFLICT,
  // equality split requested by cardinality solver
  //  (or (= t1 t2) (not (= t1 t2))
  // to satisfy the cardinality constraints on the type of t1, t2.
  UF_CARD_SPLIT,
  //-------------------- end cardinality extension to UF
  //-------------------- HO extension to UF
  // Encodes an n-ary application as a chain of binary HO_APPLY applications
  //   (= (f t1 ... tn) (@ (@ ... (@ f t1) ...) tn))
  UF_HO_APP_ENCODE,
  // A lemma corresponding to the definition of a skolem k used to convert
  // HO_APPLY terms to APPLY_UF terms. This is of the form:
  //   (forall x1 ... xn) (@ (@ k x1) ... xn) = t
  // where notice that t is a function whose free variables (if any) are
  // x1 ... xn.
  UF_HO_APP_CONV_SKOLEM,
  // Adds an extensionality lemma to witness that disequal functions have
  // different applications
  //   (not (= (f sk1 .. skn) (g sk1 .. skn))
  UF_HO_EXTENSIONALITY,
  //-------------------- model-construction specific part
  // These rules are necessary to ensure that we build models properly. For more
  // details see Section 3.3 of Barbosa et al. CADE'19.
  //
  // Enforces that a regular APPLY_UF term in the model is equal to its HO_APPLY
  // equivalent by adding the equality as a lemma
  //   (= (f t1 ... tn) (@ (@ ... (@ f t1) ...) tn))
  UF_HO_MODEL_APP_ENCODE,
  // Adds an extensionality lemma to witness that disequal functions have
  // different applications
  //   (not (= (f sk1 .. skn) (g sk1 .. skn))
  UF_HO_MODEL_EXTENSIONALITY,
  // equivalence of lambda functions
  //   f = g => forall x. reduce(lambda(f)(x)) = reduce(lambda(g)(x))
  // This is applied when lamda functions f and g are in the same eq class.
  UF_HO_LAMBDA_UNIV_EQ,
  // equivalence of a lambda function and an ordinary function
  //   f = h => h(t) = reduce(lambda(f)(t))
  // This is applied when lamda function f and ordinary function h are in the
  // same eq class.
  UF_HO_LAMBDA_APP_REDUCE,
  //-------------------- end model-construction specific part
  //-------------------- end HO extension to UF
  //-------------------- UF arith/bv conversions solver
  // reductions of an arithmetic/bit-vector conversion term
  UF_ARITH_BV_CONV_REDUCTION,
  //-------------------------------------- end uf theory

  //-------------------------------------- unknown
  UNKNOWN
};

/**
 * Converts an inference to a string. Note: This function is also used in
 * `safe_print()`. Changing this functions name or signature will result in
 * `safe_print()` printing "<unsupported>" instead of the proper strings for
 * the enum values.
 *
 * @param i The inference
 * @return The name of the inference
 */
const char* toString(InferenceId i);

/**
 * Writes an inference name to a stream.
 *
 * @param out The stream to write to
 * @param i The inference to write to the stream
 * @return The stream
 */
std::ostream& operator<<(std::ostream& out, InferenceId i);

/** Make node from inference id */
Node mkInferenceIdNode(InferenceId i);

/** get an inference identifier from a node, return false if we fail */
bool getInferenceId(TNode n, InferenceId& i);

}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5__THEORY__INFERENCE_H */
