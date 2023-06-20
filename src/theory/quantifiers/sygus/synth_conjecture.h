/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Abdalrhman Mohamed, Haniel Barbosa
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Class that encapsulates techniques for a single (SyGuS) synthesis
 * conjecture.
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__QUANTIFIERS__SYNTH_CONJECTURE_H
#define CVC5__THEORY__QUANTIFIERS__SYNTH_CONJECTURE_H

#include <memory>

#include "smt/env_obj.h"
#include "theory/quantifiers/expr_miner_manager.h"
#include "theory/quantifiers/sygus/ce_guided_single_inv.h"
#include "theory/quantifiers/sygus/cegis.h"
#include "theory/quantifiers/sygus/cegis_core_connective.h"
#include "theory/quantifiers/sygus/cegis_unif.h"
#include "theory/quantifiers/sygus/enum_val_generator.h"
#include "theory/quantifiers/sygus/example_eval_cache.h"
#include "theory/quantifiers/sygus/example_infer.h"
#include "theory/quantifiers/sygus/sygus_process_conj.h"
#include "theory/quantifiers/sygus/sygus_repair_const.h"
#include "theory/quantifiers/sygus/sygus_stats.h"
#include "theory/quantifiers/sygus/synth_verify.h"
#include "theory/quantifiers/sygus/template_infer.h"

namespace cvc5::internal {
namespace theory {
namespace quantifiers {

class EmbeddingConverter;
class SygusPbe;
class SygusStatistics;
class EnumValueManager;

/** a synthesis conjecture
 * This class implements approaches for a synthesis conjecture, given by data
 * member d_quant.
 * This includes both approaches for synthesis in Reynolds et al CAV 2015. It
 * determines which approach and optimizations are applicable to the
 * conjecture, and has interfaces for implementing them.
 */
class SynthConjecture : protected EnvObj
{
 public:
  SynthConjecture(Env& env,
                  QuantifiersState& qs,
                  QuantifiersInferenceManager& qim,
                  QuantifiersRegistry& qr,
                  TermRegistry& tr,
                  SygusStatistics& s);
  ~SynthConjecture();
  /**
   * Presolve, called once at the beginning of every check-sat.
   */
  void presolve();
  /** get original version of conjecture */
  Node getConjecture() const { return d_quant; }
  /** get deep embedding version of conjecture */
  Node getEmbeddedConjecture() const { return d_embed_quant; }
  //-------------------------------for counterexample-guided check/refine
  /** whether the conjecture is waiting for a call to doCheck below */
  bool needsCheck();
  /** do syntax-guided enumerative check
   *
   * This is step 2(a) of Figure 3 of Reynolds et al CAV 2015.
   *
   * The method returns true if this conjecture is finished trying solutions
   * for the given call to SynthEngine::check.
   *
   * Notice that we make multiple calls to doCheck on one call to
   * SynthEngine::check. For example, if we are using an actively-generated
   * enumerator, one enumerated (abstract) term may correspond to multiple
   * concrete terms t1, ..., tn to check, where we make up to n calls to doCheck
   * when each of t1, ..., tn fails to satisfy the current refinement lemmas.
   */
  bool doCheck();
  //-------------------------------end for counterexample-guided check/refine
  /** get synth solutions
   *
   * This method returns true if this class has a solution available to the
   * conjecture that it was assigned.
   *
   * Let q be the synthesis conjecture assigned to this class.
   * This method adds entries to sol_map[q] that map functions-to-synthesize to
   * their builtin solution, which has the same type. For example, for synthesis
   * conjecture exists f. forall x. f( x )>x, this function will update
   * sol_map[q] to contain the entry:
   *   f -> (lambda x. x+1)
   */
  bool getSynthSolutions(std::map<Node, std::map<Node, Node> >& sol_map);
  /** is ground */
  bool isGround() const { return d_innerVars.empty(); }
  /** are we using single invocation techniques */
  bool isSingleInvocation() const;
  /** preprocess notify conjecture
   * This is used as a heuristic for solution reconstruction, so that we
   * remember expressions in the conjecture before preprocessing, since they
   * may be helpful during solution reconstruction (Figure 5 of Reynolds et al
   * CAV 2015)
   */
  void ppNotifyConjecture(Node q);
  /** assign conjecture q to this class */
  void assign(Node q);
  /** has a conjecture been assigned to this class */
  bool isAssigned() { return !d_embed_quant.isNull(); }
  /**
   * Get model value for term n.
   */
  Node getModelValue(Node n);

  /** get utility for static preprocessing and analysis of conjectures */
  SynthConjectureProcess* getProcess() { return d_ceg_proc.get(); }
  /** get constant repair utility */
  SygusRepairConst* getRepairConst() { return d_sygus_rconst.get(); }
  /** get example inference utility */
  ExampleInfer* getExampleInfer() { return d_exampleInfer.get(); }
  /** get the example evaluation cache utility for enumerator e */
  ExampleEvalCache* getExampleEvalCache(Node e);
  /** get program by examples module */
  SygusPbe* getPbe() { return d_ceg_pbe.get(); }
  /** get the symmetry breaking predicate for type */
  Node getSymmetryBreakingPredicate(
      Node x, Node e, TypeNode tn, unsigned tindex, unsigned depth);
  /** print out debug information about this conjecture */
  void debugPrint(const char* c);
  /** check side condition
   *
   * This returns false if the solution { d_candidates -> cvals } does not
   * satisfy the side condition of the conjecture maintained by this class,
   * if it exists, and true otherwise.
   */
  bool checkSideCondition(const std::vector<Node>& cvals);

  /** get a reference to the statistics of parent */
  SygusStatistics& getSygusStatistics() { return d_stats; };

  /** exclude the current solution { enums -> values } due to id */
  void excludeCurrentSolution(const std::vector<Node>& values, InferenceId id);

 private:
  /** do refinement
   *
   * This is step 2(b) of Figure 3 of Reynolds et al CAV 2015.
   *
   * This method is run when skModel is corresponds to a counterexample to the
   * last candidate in the doCheck method.
   *
   * This method adds a refinement lemma on the output channel of quantifiers
   * engine. If the refinement lemma is a duplicate, then we manually
   * exclude the current candidate via excludeCurrentSolution. This should
   * only occur when the synthesis conjecture for the current candidate fails
   * to evaluate to false for a given counterexample point, but regardless its
   * negation is satisfiable for the current candidate and that point. This is
   * exclusive to theories with partial functions, e.g. (non-linear) division.
   *
   * This method returns true if a lemma was added on the output channel, and
   * false otherwise.
   */
  bool processCounterexample(const std::vector<Node>& skModel);
  /** Reference to the quantifiers state */
  QuantifiersState& d_qstate;
  /** Reference to the quantifiers inference manager */
  QuantifiersInferenceManager& d_qim;
  /** The quantifiers registry */
  QuantifiersRegistry& d_qreg;
  /** Reference to the term registry */
  TermRegistry& d_treg;
  /** reference to the statistics of parent */
  SygusStatistics& d_stats;
  /** term database sygus of d_qe */
  TermDbSygus* d_tds;
  /** The synthesis verify utility */
  SynthVerify d_verify;
  /**
   * Do we have a solution in this solve context? This flag is reset to false
   * on every call to presolve.
   */
  bool d_hasSolution;
  /** Whether we have computed a solution */
  bool d_computedSolution;
  /** whether we are running expression mining */
  bool d_runExprMiner;
  /**
   * The final solution and status, caches getSynthSolutionsInternal, valid
   * if d_computedSolution is true.
   */
  std::vector<Node> d_sol;
  std::vector<int8_t> d_solStatus;
  /**
   * (SyGuS datatype) values for solutions, which is populated if we have a
   * solution and only if we are not using the single invocation solver.
   */
  std::vector<std::vector<Node>> d_solutionValues;
  /** the decision strategy for the feasible guard */
  std::unique_ptr<DecisionStrategy> d_feasible_strategy;
  /** single invocation utility */
  std::unique_ptr<CegSingleInv> d_ceg_si;
  /** template inference utility */
  std::unique_ptr<SygusTemplateInfer> d_templInfer;
  /** utility for static preprocessing and analysis of conjectures */
  std::unique_ptr<SynthConjectureProcess> d_ceg_proc;
  /** grammar utility */
  std::unique_ptr<EmbeddingConverter> d_embConv;
  /** repair constant utility */
  std::unique_ptr<SygusRepairConst> d_sygus_rconst;
  /** example inference utility */
  std::unique_ptr<ExampleInfer> d_exampleInfer;
  /** map from enumerators to their enumerator manager */
  std::map<Node, std::unique_ptr<EnumValueManager>> d_enumManager;

  //------------------------modules
  /** program by examples module */
  std::unique_ptr<SygusPbe> d_ceg_pbe;
  /** CEGIS module */
  std::unique_ptr<Cegis> d_ceg_cegis;
  /** CEGIS UNIF module */
  std::unique_ptr<CegisUnif> d_ceg_cegisUnif;
  /** connective core utility */
  std::unique_ptr<CegisCoreConnective> d_sygus_ccore;
  /** the set of active modules (subset of the above list) */
  std::vector<SygusModule*> d_modules;
  /** master module
   *
   * This is the module (one of those above) that takes sole responsibility
   * for this conjecture, determined during assign(...).
   */
  SygusModule* d_master;
  //------------------------end modules

  //------------------------enumerators
  /**
   * Get model values for terms n, store in vector v. This method returns true
   * if and only if all values added to v are non-null.
   *
   * The argument activeIncomplete indicates whether n contains an active
   * enumerator that is currently not finished enumerating values, but returned
   * null on a call to getEnumeratedValue. This value is used for determining
   * whether we should call getEnumeratedValues again within a call to
   * SynthConjecture::check.
   *
   * It removes terms from n that correspond to "inactive" enumerators, that
   * is, enumerators whose values have been exhausted.
   */
  bool getEnumeratedValues(std::vector<Node>& n,
                           std::vector<Node>& v,
                           bool& activeIncomplete);
  /**
   * Get or make enumerator manager for the enumerator e.
   */
  EnumValueManager* getEnumValueManagerFor(Node e);
  /**
   * Get or make the expression miner manager for enumerator e.
   */
  ExpressionMinerManager* getExprMinerManagerFor(Node e);
  //------------------------end enumerators

  /** list of constants for quantified formula
   * The outer Skolems for the negation of d_embed_quant.
   */
  std::vector<Node> d_candidates;
  /** base instantiation
   * If d_embed_quant is forall d. exists y. P( d, y ), then
   * this is the formula  exists y. P( d_candidates, y ). Notice that
   * (exists y. F) is shorthand above for ~( forall y. ~F ).
   */
  Node d_base_inst;
  /** The skolemized form of the above formula. */
  Node d_checkBody;
  /** list of variables on inner quantification */
  std::vector<Node> d_innerVars;
  /** list of skolems on inner quantification */
  std::vector<Node> d_innerSks;
  /** the asserted (negated) conjecture */
  Node d_quant;
  /**
   * The side condition for solving the conjecture, after conversion to deep
   * embedding.
   */
  Node d_embedSideCondition;
  /** (negated) conjecture after simplification */
  Node d_simp_quant;
  /** (negated) conjecture after simplification, conversion to deep embedding */
  Node d_embed_quant;
  /**
   * The first index of an instantiation in CandidateInfo::d_inst that we have
   * not yet tried to repair.
   */
  unsigned d_repair_index;
  /** record solution (this is used to construct solutions later) */
  void recordSolution(const std::vector<Node>& vs);
  /** get synth solutions internal
   *
   * This function constructs the body of solutions for all
   * functions-to-synthesize in this conjecture and stores them in sols, in
   * order. For each solution added to sols, we add an integer indicating what
   * kind of solution n is, where if sols[i] = n, then
   *   if status[i] = 0: n is the (builtin term) corresponding to the solution,
   *   if status[i] = 1: n is the sygus representation of the solution.
   * We store builtin versions under some conditions (such as when the sygus
   * grammar is being ignored).
   *
   * This consults the single invocation module to get synthesis solutions if
   * isSingleInvocation() returns true.
   *
   * For example, for conjecture exists fg. forall x. f(x)>g(x), this function
   * may set ( sols, status ) to ( { x+1, d_x() }, { 1, 0 } ), where d_x() is
   * the sygus datatype constructor corresponding to variable x.
   */
  bool getSynthSolutionsInternal(std::vector<Node>& sols,
                                 std::vector<int8_t>& status);
  /**
   * Run expression mining on the last synthesis solution. Return true
   * if we should skip it.
   *
   * This method also prints the current synthesis solution to output stream out
   * when sygusStream is enabled, which does not enclose solutions in
   * parentheses. If sygusStream is enabled, this always returns true, as the
   * current solution should be printed and then immediately excluded.
   */
  bool runExprMiner();
  /** expression miner managers for each function-to-synthesize
   *
   * Notice that for each function-to-synthesize, we enumerate a stream of
   * candidate solutions, where each of these streams is independent. Thus,
   * we maintain separate expression miner managers for each of them.
   *
   * This is used for the sygusRewSynth() option to synthesize new candidate
   * rewrite rules.
   */
  std::map<Node, std::unique_ptr<ExpressionMinerManager>> d_exprm;
};

}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal

#endif
