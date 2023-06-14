/******************************************************************************
 * Top contributors (to current version):
 *   Morgan Deters, Andrew Reynolds, Clark Barrett
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Theory of arrays.
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__ARRAYS__THEORY_ARRAYS_H
#define CVC5__THEORY__ARRAYS__THEORY_ARRAYS_H

#include <tuple>
#include <unordered_map>

#include "context/cdhashmap.h"
#include "context/cdhashset.h"
#include "context/cdqueue.h"
#include "theory/arrays/array_info.h"
#include "theory/arrays/inference_manager.h"
#include "theory/arrays/proof_checker.h"
#include "theory/arrays/theory_arrays_rewriter.h"
#include "theory/decision_strategy.h"
#include "theory/theory.h"
#include "theory/theory_state.h"
#include "theory/uf/equality_engine.h"
#include "util/statistics_stats.h"

namespace cvc5::internal {
namespace theory {
namespace arrays {

/**
 * Decision procedure for arrays.
 *
 * Overview of decision procedure:
 *
 * Preliminary notation:
 *   Stores(a)  = {t | a ~ t and t = store( _ _ _ )}
 *   InStores(a) = {t | t = store (b _ _) and a ~ b }
 *   Indices(a) = {i | there exists a term b[i] such that a ~ b or store(b i v)}
 *   ~ represents the equivalence relation based on the asserted equalities in the
 *   current context.
 *
 * The rules implemented are the following:
 *             store(b i v)
 *     Row1 -------------------
 *          store(b i v)[i] = v
 *
 *           store(b i v)  a'[j]
 *     Row ---------------------- [ a' ~ store(b i v) or a' ~ b ]
 *           i = j OR a[j] = b[j]
 *
 *          a  b same kind arrays
 *     Ext ------------------------ [ a!= b in current context, k new var]
 *           a = b OR a[k] != b[k]p
 *
 *
 *  The Row1 one rule is implemented implicitly as follows:
 *     - for each store(b i v) term add the following equality to the congruence
 *       closure store(b i v)[i] = v
 *     - if one of the literals in a conflict is of the form store(b i v)[i] = v
 *       remove it from the conflict
 *
 *  Because new store terms are not created, we need to check if we need to
 *  instantiate a new Row axiom in the following cases:
 *     1. the congruence relation changes (i.e. two terms get merged)
 *         - when a new equality between array terms a = b is asserted we check if
 *           we can instantiate a Row lemma for all pairs of indices i where a is
 *           being read and stores
 *         - this is only done during full effort check
 *     2. a new read term is created either as a consequences of an Ext lemma or a
 *        Row lemma
 *         - this is implemented in the checkRowForIndex method which is called
 *           when preregistering a term of the form a[i].
 *         - as a consequence lemmas are instantiated even before full effort check
 *
 *  The Ext axiom is instantiated when a disequality is asserted during full effort
 *  check. Ext lemmas are stored in a cache to prevent instantiating essentially
 *  the same lemma multiple times.
 */

static inline std::string spaces(int level)
{
  std::string indentStr(level, ' ');
  return indentStr;
}

class TheoryArrays : public Theory {

  /////////////////////////////////////////////////////////////////////////////
  // MISC
  /////////////////////////////////////////////////////////////////////////////

 private:

  /** True node for predicates = true */
  Node d_true;

  /** True node for predicates = false */
  Node d_false;

  // Statistics

  /** number of Row lemmas */
  IntStat d_numRow;
  /** number of Ext lemmas */
  IntStat d_numExt;
  /** number of propagations */
  IntStat d_numProp;
  /** number of explanations */
  IntStat d_numExplain;
  /** calls to non-linear */
  IntStat d_numNonLinear;
  /** splits on array variables */
  IntStat d_numSharedArrayVarSplits;
  /** splits in getModelVal */
  IntStat d_numGetModelValSplits;
  /** conflicts in getModelVal */
  IntStat d_numGetModelValConflicts;
  /** splits in setModelVal */
  IntStat d_numSetModelValSplits;
  /** conflicts in setModelVal */
  IntStat d_numSetModelValConflicts;

 public:
  TheoryArrays(Env& env,
               OutputChannel& out,
               Valuation valuation,
               std::string name = "theory::arrays::");
  ~TheoryArrays();

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

  std::string identify() const override { return std::string("TheoryArrays"); }

  /////////////////////////////////////////////////////////////////////////////
  // PREPROCESSING
  /////////////////////////////////////////////////////////////////////////////

 private:

  // PPNotifyClass: dummy template class for d_ppEqualityEngine - notifications not used
  class PPNotifyClass {
  public:
    bool notify(TNode propagation) { return true; }
    void notify(TNode t1, TNode t2) { }
  };

  /** The notify class for d_ppEqualityEngine */
  PPNotifyClass d_ppNotify;

  /** Equaltity engine */
  eq::EqualityEngine d_ppEqualityEngine;

  // List of facts learned by preprocessor - needed for permanent ref for benefit of d_ppEqualityEngine
  context::CDList<Node> d_ppFacts;

  Node preprocessTerm(TNode term);
  Node recursivePreprocessTerm(TNode term);
  bool ppDisequal(TNode a, TNode b);
  Node solveWrite(TNode term, bool solve1, bool solve2, bool ppCheck);

  /** The theory rewriter for this theory. */
  TheoryArraysRewriter d_rewriter;
  /** A (default) theory state object */
  TheoryState d_state;
  /** The arrays inference manager */
  InferenceManager d_im;

 public:
  PPAssertStatus ppAssert(TrustNode tin,
                          TrustSubstitutionMap& outSubstitutions) override;
  TrustNode ppRewrite(TNode atom, std::vector<SkolemLemma>& lems) override;

  /////////////////////////////////////////////////////////////////////////////
  // T-PROPAGATION / REGISTRATION
  /////////////////////////////////////////////////////////////////////////////

 private:
  /** Literals to propagate */
  context::CDList<Node> d_literalsToPropagate;

  /** Index of the next literal to propagate */
  context::CDO<unsigned> d_literalsToPropagateIndex;

  /** Should be called to propagate the literal.  */
  bool propagateLit(TNode literal);

  /** For debugging only- checks invariants about when things are preregistered*/
  context::CDHashSet<Node> d_isPreRegistered;

  /** Helper for preRegisterTerm, also used internally */
  void preRegisterTermInternal(TNode n);

 public:
  void preRegisterTerm(TNode n) override;
  TrustNode explain(TNode n) override;

  /////////////////////////////////////////////////////////////////////////////
  // SHARING
  /////////////////////////////////////////////////////////////////////////////

 private:
  class MayEqualNotifyClass {
  public:
    bool notify(TNode propagation) { return true; }
    void notify(TNode t1, TNode t2) { }
  };

  /** The notify class for d_mayEqualEqualityEngine */
  MayEqualNotifyClass d_mayEqualNotify;

  /** Equaltity engine for determining if two arrays might be equal */
  eq::EqualityEngine d_mayEqualEqualityEngine;

  // Helper for computeCareGraph
  void checkPair(TNode r1, TNode r2);

 public:
  void notifySharedTerm(TNode t) override;
  void computeCareGraph() override;
  bool isShared(TNode t)
  {
    return (d_sharedArrays.find(t) != d_sharedArrays.end());
  }

  /////////////////////////////////////////////////////////////////////////////
  // MODEL GENERATION
  /////////////////////////////////////////////////////////////////////////////

 public:
  /** Collect model values in m based on the relevant terms given by termSet */
  bool collectModelValues(TheoryModel* m,
                          const std::set<Node>& termSet) override;

  /////////////////////////////////////////////////////////////////////////////
  // NOTIFICATIONS
  /////////////////////////////////////////////////////////////////////////////


  void presolve() override;

  /////////////////////////////////////////////////////////////////////////////
  // MAIN SOLVER
  /////////////////////////////////////////////////////////////////////////////

  //--------------------------------- standard check
  /** Post-check, called after the fact queue of the theory is processed. */
  void postCheck(Effort level) override;
  /** Pre-notify fact, return true if processed. */
  bool preNotifyFact(TNode atom,
                     bool pol,
                     TNode fact,
                     bool isPrereg,
                     bool isInternal) override;
  /** Notify fact */
  void notifyFact(TNode atom, bool pol, TNode fact, bool isInternal) override;
  //--------------------------------- end standard check

 private:
  TNode weakEquivGetRep(TNode node);
  TNode weakEquivGetRepIndex(TNode node, TNode index);
  void visitAllLeaves(TNode reason, std::vector<TNode>& conjunctions);
  void weakEquivBuildCond(TNode node, TNode index, std::vector<TNode>& conjunctions);
  void weakEquivMakeRep(TNode node);
  void weakEquivMakeRepIndex(TNode node);
  void weakEquivAddSecondary(TNode index, TNode arrayFrom, TNode arrayTo, TNode reason);
  void checkWeakEquiv(bool arraysMerged);

  // NotifyClass: template helper class for d_equalityEngine - handles call-back from congruence closure module
  class NotifyClass : public eq::EqualityEngineNotify {
    TheoryArrays& d_arrays;
  public:
    NotifyClass(TheoryArrays& arrays): d_arrays(arrays) {}

    bool eqNotifyTriggerPredicate(TNode predicate, bool value) override
    {
      Trace("arrays::propagate")
          << spaces(d_arrays.context()->getLevel())
          << "NotifyClass::eqNotifyTriggerPredicate(" << predicate << ", "
          << (value ? "true" : "false") << ")" << std::endl;
      // Just forward to arrays
      if (value) {
        return d_arrays.propagateLit(predicate);
      }
      return d_arrays.propagateLit(predicate.notNode());
    }

    bool eqNotifyTriggerTermEquality(TheoryId tag,
                                     TNode t1,
                                     TNode t2,
                                     bool value) override
    {
      Trace("arrays::propagate")
          << spaces(d_arrays.context()->getLevel())
          << "NotifyClass::eqNotifyTriggerTermEquality(" << t1 << ", " << t2
          << ", " << (value ? "true" : "false") << ")" << std::endl;
      if (value) {
        // Propagate equality between shared terms
        return d_arrays.propagateLit(t1.eqNode(t2));
      }
      return d_arrays.propagateLit(t1.eqNode(t2).notNode());
    }

    void eqNotifyConstantTermMerge(TNode t1, TNode t2) override
    {
      Trace("arrays::propagate") << spaces(d_arrays.context()->getLevel())
                                 << "NotifyClass::eqNotifyConstantTermMerge("
                                 << t1 << ", " << t2 << ")" << std::endl;
      d_arrays.conflict(t1, t2);
    }

    void eqNotifyNewClass(TNode t) override
    {
      d_arrays.preRegisterTermInternal(t);
    }
    void eqNotifyMerge(TNode t1, TNode t2) override
    {
      if (t1.getType().isArray()) {
        d_arrays.mergeArrays(t1, t2);
      }
    }
    void eqNotifyDisequal(TNode t1, TNode t2, TNode reason) override {}
  };

  /** The notify class for d_equalityEngine */
  NotifyClass d_notify;

  /** The proof checker */
  ArraysProofRuleChecker d_checker;

  /** Conflict when merging constants */
  void conflict(TNode a, TNode b);

  /** The conflict node */
  Node d_conflictNode;

  /**
   * Context dependent map from a congruence class canonical representative of
   * type array to an Info pointer that keeps track of information useful to axiom
   * instantiation
   */
  ArrayInfo d_infoMap;

  context::CDQueue<Node> d_mergeQueue;

  bool d_mergeInProgress;

  using RowLemmaType = std::tuple<TNode, TNode, TNode, TNode>;

  context::CDQueue<RowLemmaType> d_RowQueue;
  context::CDHashSet<RowLemmaType, RowLemmaTypeHashFunction> d_RowAlreadyAdded;

  typedef context::CDHashSet<Node> CDNodeSet;

  CDNodeSet d_sharedArrays;
  CDNodeSet d_sharedOther;
  context::CDO<bool> d_sharedTerms;

  // Map from constant values to read terms that read from that values equal to that constant value in the current model
  // When a new read term is created, we check the index to see if we know the model value.  If so, we add it to d_constReads (and d_constReadsList)
  // If not, we push it onto d_reads and figure out where it goes at computeCareGraph time.
  // d_constReadsList is used as a backup in case we can't compute the model at computeCareGraph time.
  typedef std::unordered_map<Node, CTNodeList*> CNodeNListMap;
  CNodeNListMap d_constReads;
  context::CDList<TNode> d_reads;
  context::CDList<TNode> d_constReadsList;
  context::Context* d_constReadsContext;
  /** Helper class to keep d_constReadsContext in sync with satContext */
  class ContextPopper : public context::ContextNotifyObj
  {
    context::Context* d_satContext;
    context::Context* d_contextToPop;

   protected:
    void contextNotifyPop() override
    {
      if (d_contextToPop->getLevel() > d_satContext->getLevel())
      {
        d_contextToPop->pop();
      }
    }

   public:
    ContextPopper(context::Context* context, context::Context* contextToPop)
        : context::ContextNotifyObj(context),
          d_satContext(context),
          d_contextToPop(contextToPop)
    {
    }

  }; /* class ContextPopper */
  ContextPopper d_contextPopper;

  // The decision requests we have for the core
  context::CDQueue<Node> d_decisionRequests;

  // List of nodes that need permanent references in this context
  context::CDList<Node> d_permRef;
  context::CDList<Node> d_modelConstraints;
  context::CDHashSet<Node> d_lemmasSaved;
  std::vector<Node> d_lemmas;

  // Default values for each mayEqual equivalence class
  typedef context::CDHashMap<Node, Node> DefValMap;
  DefValMap d_defValues;

  typedef std::unordered_map<std::pair<TNode, TNode>, CTNodeList*, TNodePairHashFunction> ReadBucketMap;
  ReadBucketMap d_readBucketTable;
  context::Context* d_readTableContext;
  context::CDList<Node> d_arrayMerges;
  std::vector<CTNodeList*> d_readBucketAllocations;

  Node getSkolem(TNode ref);
  Node mkAnd(std::vector<TNode>& conjunctions, bool invert = false, unsigned startIndex = 0);
  void setNonLinear(TNode a);
  Node removeRepLoops(TNode a, TNode rep);
  Node expandStores(TNode s, std::vector<TNode>& assumptions, bool checkLoop = false, TNode a = TNode(), TNode b = TNode());
  void mergeArrays(TNode a, TNode b);
  void checkStore(TNode a);
  void checkRowForIndex(TNode i, TNode a);
  void checkRowLemmas(TNode a, TNode b);
  void propagateRowLemma(RowLemmaType lem);
  void queueRowLemma(RowLemmaType lem);
  bool dischargeLemmas();

  /**
   * The decision strategy for the theory of arrays, which calls the
   * getNextDecisionEngineRequest function below.
   */
  class TheoryArraysDecisionStrategy : public DecisionStrategy
  {
   public:
    TheoryArraysDecisionStrategy(TheoryArrays* ta);
    /** initialize */
    void initialize() override;
    /** get next decision request */
    Node getNextDecisionRequest() override;
    /** identify */
    std::string identify() const override;

   private:
    /** pointer to the theory of arrays */
    TheoryArrays* d_ta;
  };
  /** an instance of the above decision strategy */
  std::unique_ptr<TheoryArraysDecisionStrategy> d_dstrat;
  /** Have we registered the above strategy? (context-independent) */
  bool d_dstratInit;
  /** get the next decision request
   *
   * If the "arrays-eager-index" option is enabled, then whenever a
   * read-over-write lemma is generated, a decision request is also generated
   * for the comparison between the indexes that appears in the lemma.
   */
  Node getNextDecisionRequest();
  /**
   * Compute relevant terms. This includes select nodes for the
   * RIntro1 and RIntro2 rules.
   */
  void computeRelevantTerms(std::set<Node>& termSet) override;
};/* class TheoryArrays */

}  // namespace arrays
}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5__THEORY__ARRAYS__THEORY_ARRAYS_H */
