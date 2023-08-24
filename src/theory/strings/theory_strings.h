/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Tianyi Liang, Andres Noetzli
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Theory of strings.
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__STRINGS__THEORY_STRINGS_H
#define CVC5__THEORY__STRINGS__THEORY_STRINGS_H

#include <climits>
#include <deque>

#include "context/cdhashset.h"
#include "context/cdlist.h"
#include "expr/node_trie.h"
#include "theory/care_pair_argument_callback.h"
#include "theory/ext_theory.h"
#include "theory/strings/array_solver.h"
#include "theory/strings/base_solver.h"
#include "theory/strings/code_point_solver.h"
#include "theory/strings/core_solver.h"
#include "theory/strings/eager_solver.h"
#include "theory/strings/extf_solver.h"
#include "theory/strings/infer_info.h"
#include "theory/strings/inference_manager.h"
#include "theory/strings/model_cons_default.h"
#include "theory/strings/normal_form.h"
#include "theory/strings/proof_checker.h"
#include "theory/strings/regexp_elim.h"
#include "theory/strings/regexp_operation.h"
#include "theory/strings/regexp_solver.h"
#include "theory/strings/sequences_stats.h"
#include "theory/strings/solver_state.h"
#include "theory/strings/strategy.h"
#include "theory/strings/strings_fmf.h"
#include "theory/strings/strings_rewriter.h"
#include "theory/strings/term_registry.h"
#include "theory/theory.h"
#include "theory/uf/equality_engine.h"

namespace cvc5::internal {
namespace theory {
namespace strings {

/**
 * A theory solver for strings. At a high level, the solver implements
 * techniques described in:
 * - Liang et al, CAV 2014,
 * - Reynolds et al, CAV 2017,
 * - Reynolds et al, IJCAR 2020.
 * Its rewriter is described in:
 * - Reynolds et al, CAV 2019.
 */
class TheoryStrings : public Theory {
  friend class InferenceManager;
  typedef context::CDHashSet<Node> NodeSet;
  typedef context::CDHashSet<TypeNode, std::hash<TypeNode>> TypeNodeSet;

 public:
  TheoryStrings(Env& env, OutputChannel& out, Valuation valuation);
  ~TheoryStrings();
  //--------------------------------- initialization
  /** get the official theory rewriter of this theory */
  TheoryRewriter* getTheoryRewriter() override;
  /** get the proof checker of this theory */
  ProofRuleChecker* getProofChecker() override;
  /**
   * Returns true if we need an equality engine. If so, we initialize the
   * information regarding how it should be setup. For details, see the
   * documentation in Theory::needsEqualityEngine.
   */
  bool needsEqualityEngine(EeSetupInfo& esi) override;
  /** finish initialization */
  void finishInit() override;
  //--------------------------------- end initialization
  /** Identify this theory */
  std::string identify() const override;
  /** Explain */
  TrustNode explain(TNode literal) override;
  /** presolve */
  void presolve() override;
  /** preregister term */
  void preRegisterTerm(TNode n) override;
  //--------------------------------- standard check
  /** Do we need a check call at last call effort? */
  bool needsCheckLastEffort() override;
  bool preNotifyFact(TNode atom,
                     bool pol,
                     TNode fact,
                     bool isPrereg,
                     bool isInternal) override;
  void notifyFact(TNode atom, bool pol, TNode fact, bool isInternal) override;
  /** Post-check, called after the fact queue of the theory is processed. */
  void postCheck(Effort level) override;
  //--------------------------------- end standard check
  /** propagate method */
  bool propagateLit(TNode literal);
  /** Conflict when merging two constants */
  void conflict(TNode a, TNode b);
  /** called when a new equivalence class is created */
  void eqNotifyNewClass(TNode t);
  /** Called just after the merge of two equivalence classes */
  void eqNotifyMerge(TNode t1, TNode t2);
  /** preprocess rewrite */
  TrustNode ppRewrite(TNode atom, std::vector<SkolemLemma>& lems) override;
  TrustNode ppStaticRewrite(TNode atom) override;
  /** Collect model values in m based on the relevant terms given by termSet */
  bool collectModelValues(TheoryModel* m,
                          const std::set<Node>& termSet) override;

 private:
  /** NotifyClass for equality engine */
  class NotifyClass : public eq::EqualityEngineNotify {
  public:
   NotifyClass(TheoryStrings& ts) : d_str(ts) {}
   bool eqNotifyTriggerPredicate(TNode predicate, bool value) override
   {
     Trace("strings") << "NotifyClass::eqNotifyTriggerPredicate(" << predicate
                      << ", " << (value ? "true" : "false") << ")" << std::endl;
     if (value)
     {
       return d_str.propagateLit(predicate);
     }
     return d_str.propagateLit(predicate.notNode());
    }
    bool eqNotifyTriggerTermEquality(TheoryId tag,
                                     TNode t1,
                                     TNode t2,
                                     bool value) override
    {
      Trace("strings") << "NotifyClass::eqNotifyTriggerTermMerge(" << tag << ", " << t1 << ", " << t2 << ")" << std::endl;
      if (value) {
        return d_str.propagateLit(t1.eqNode(t2));
      }
      return d_str.propagateLit(t1.eqNode(t2).notNode());
    }
    void eqNotifyConstantTermMerge(TNode t1, TNode t2) override
    {
      Trace("strings") << "NotifyClass::eqNotifyConstantTermMerge(" << t1 << ", " << t2 << ")" << std::endl;
      d_str.conflict(t1, t2);
    }
    void eqNotifyNewClass(TNode t) override
    {
      Trace("strings") << "NotifyClass::eqNotifyNewClass(" << t << std::endl;
      d_str.eqNotifyNewClass(t);
    }
    void eqNotifyMerge(TNode t1, TNode t2) override
    {
      Trace("strings") << "NotifyClass::eqNotifyMerge(" << t1 << ", " << t2
                       << std::endl;
      d_str.eqNotifyMerge(t1, t2);
    }
    void eqNotifyDisequal(TNode t1, TNode t2, TNode reason) override
    {
    }

   private:
    /** The theory of strings object to notify */
    TheoryStrings& d_str;
  };/* class TheoryStrings::NotifyClass */
  /** compute care graph */
  void computeCareGraph() override;
  /** notify shared term */
  void notifySharedTerm(TNode n) override;
  /** Collect model info for type tn
   *
   * Assigns model values (in m) to all relevant terms of the string-like type
   * tn in the current context, which are stored in repSet[tn].
   *
   * @param tn The type to compute model values for
   * @param toProcess Remaining types to compute model values for
   * @param repSet A map of types to representatives of
   * the equivalence classes of the given type
   * @return false if a conflict is discovered while doing this assignment.
   */
  bool collectModelInfoType(
      TypeNode tn,
      std::unordered_set<TypeNode>& toProcess,
      const std::map<TypeNode, std::unordered_set<Node>>& repSet,
      TheoryModel* m);

  /** assert pending fact
   *
   * This asserts atom with polarity to the equality engine of this class,
   * where exp is the explanation of why (~) atom holds.
   *
   * This call may trigger further initialization steps involving the terms
   * of atom, including calls to registerTerm.
   */
  void assertPendingFact(Node atom, bool polarity, Node exp);
  /**
   * Turn a sequence constant into a skeleton specifying how to construct
   * its value.
   * In particular, this means that value:
   *   (seq.++ (seq.unit 0) (seq.unit 1) (seq.unit 2))
   * becomes:
   *   (seq.++ (seq.unit k_0) (seq.unit k_1) (seq.unit k_2))
   * where k_0, k_1, k_2 are fresh integer variables. These
   * variables will be assigned values in the standard way by the
   * model. This construction is necessary during model construction since the
   * strings solver must constrain the length of the model of an equivalence
   * class (e.g. in this case to length 3); moreover we cannot assign a concrete
   * value since it may conflict with other skeletons we have assigned.
   */
  Node mkSkeletonFor(Node value);
  /**
   * Make the skeleton for the basis of constructing sequence r between
   * indices currIndex (inclusive) and nextIndex (exclusive). For example, if
   * currIndex = 2 and nextIndex = 5, then this returns:
   *   (seq.++ (seq.unit k_{r,2}) (seq.unit k_{r,3}) (seq.unit k_{r,4}))
   * where k_{r,2}, k_{r,3}, k_{r,4} are Skolem variables of the element type
   * of r that are unique to the pairs (r,2), (r,3), (r,4). In other words,
   * these Skolems abstractly represent the element at positions 2, 3, 4 in the
   * model for r.
   */
  Node mkSkeletonFromBase(Node r, size_t currIndex, size_t nextIndex);
  //-----------------------end inference steps
  /** run the given inference step */
  void runInferStep(InferStep s, Theory::Effort e, int effort);
  /** run strategy for effort e */
  void runStrategy(Theory::Effort e);
  /** print strings equivalence classes for debugging */
  std::string debugPrintStringsEqc();
  /** Commonly used constants */
  Node d_true;
  Node d_false;
  Node d_zero;
  Node d_one;
  Node d_neg_one;
  /** The notify class */
  NotifyClass d_notify;
  /**
   * Statistics for the theory of strings/sequences. All statistics for these
   * theories is collected in this object.
   */
  SequencesStatistics d_statistics;
  /** The solver state object */
  SolverState d_state;
  /** The term registry for this theory */
  TermRegistry d_termReg;
  /** The theory rewriter for this theory. */
  StringsRewriter d_rewriter;
  /** The eager solver */
  std::unique_ptr<EagerSolver> d_eagerSolver;
  /** The extended theory callback */
  StringsExtfCallback d_extTheoryCb;
  /** The (custom) output channel of the theory of strings */
  InferenceManager d_im;
  /** Extended theory, responsible for context-dependent simplification. */
  ExtTheory d_extTheory;
  /** The proof rule checker */
  StringProofRuleChecker d_checker;
  /**
   * The base solver, responsible for reasoning about congruent terms and
   * inferring constants for equivalence classes.
   */
  BaseSolver d_bsolver;
  /**
   * The core solver, responsible for reasoning about string concatenation
   * with length constraints.
   */
  CoreSolver d_csolver;
  /**
   * Extended function solver, responsible for reductions and simplifications
   * involving extended string functions.
   */
  ExtfSolver d_esolver;
  /** Code point solver */
  CodePointSolver d_psolver;
  /**
   * The array solver, which implements specialized approaches for
   * seq.nth/seq.update.
   */
  ArraySolver d_asolver;
  /** regular expression solver module */
  RegExpSolver d_rsolver;
  /** regular expression elimination module */
  RegExpElimination d_regexp_elim;
  /** Strings finite model finding decision strategy */
  StringsFmf d_stringsFmf;
  /** Model constructor (default) */
  ModelConsDefault d_mcd;
  /** The representation of the strategy */
  Strategy d_strat;
  /**
   * For model building, a counter on the number of abstract witness terms
   * we have built, so that unique debug names can be assigned.
   */
  size_t d_absModelCounter;
  /**
   * For model building, a counter on the number of gaps constructed for
   * string terms due to array reasoning. This is to allocate unique unspecified
   * characters.
   */
  size_t d_strGapModelCounter;
  /** The care pair argument callback, used for theory combination */
  CarePairArgumentCallback d_cpacb;
};/* class TheoryStrings */

}  // namespace strings
}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5__THEORY__STRINGS__THEORY_STRINGS_H */
