/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Relevance manager.
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__RELEVANCE_MANAGER__H
#define CVC5__THEORY__RELEVANCE_MANAGER__H

#include <unordered_map>
#include <unordered_set>

#include "context/cdlist.h"
#include "expr/node.h"
#include "theory/difficulty_manager.h"
#include "theory/valuation.h"

namespace cvc5 {
namespace theory {

class TheoryModel;

/**
 * This class manages queries related to relevance of asserted literals.
 * In particular, note the following definition:
 *
 * Let F be a formula, and let L = { l_1, ..., l_n } be a set of
 * literals that propositionally entail it. A "relevant selection of L with
 * respect to F" is a subset of L that also propositionally entails F.
 *
 * This class computes a relevant selection of the current assertion stack
 * at FULL effort with respect to the input formula + theory lemmas that are
 * critical to justify (see LemmaProperty::NEEDS_JUSTIFY). By default, theory
 * lemmas are not critical to justify; in fact, all T-valid theory lemmas
 * are not critical to justify, since they are guaranteed to be satisfied in
 * all inputs. However, some theory lemmas that introduce skolems need
 * justification.
 *
 * As an example of such a lemma, take the example input formula:
 *   (and (exists ((x Int)) (P x)) (not (P 0)))
 * A skolemization lemma like the following needs justification:
 *   (=> (exists ((x Int)) (P x)) (P k))
 * Intuitively, this is because the satisfiability of the existential above is
 * being deferred to the satisfiability of (P k) where k is fresh. Thus,
 * a relevant selection must include both (exists ((x Int)) (P x)) and (P k)
 * in this example.
 *
 * Theories are responsible for marking such lemmas using the NEEDS_JUSTIFY
 * property when calling OutputChannel::lemma.
 *
 * Notice that this class has some relation to the justification decision
 * heuristic (--decision=justification), which constructs a relevant selection
 * of the input formula by construction. This class is orthogonal to this
 * method, since it computes relevant selection *after* a full assignment. Thus
 * its main advantage with respect to decision=justification is that it can be
 * used in combination with any SAT decision heuristic.
 *
 * Internally, this class stores the input assertions and can be asked if an
 * asserted literal is part of the current relevant selection. The relevant
 * selection is computed lazily, i.e. only when someone asks if a literal is
 * relevant, and only at most once per FULL effort check.
 */
class RelevanceManager
{
  typedef context::CDList<Node> NodeList;

 public:
  /**
   * @param lemContext The context which lemmas live at
   * @param val The valuation class, for computing what is relevant.
   */
  RelevanceManager(context::Context* lemContext, Valuation val);
  /**
   * Notify (preprocessed) assertions. This is called for input formulas or
   * lemmas that need justification that have been fully processed, just before
   * adding them to the PropEngine.
   */
  void notifyPreprocessedAssertions(const std::vector<Node>& assertions);
  /** Singleton version of above */
  void notifyPreprocessedAssertion(Node n);
  /**
   * Begin round, called at the beginning of a check in TheoryEngine.
   */
  void beginRound();
  /**
   * Is lit part of the current relevant selection? This computes the set of
   * relevant assertions if not already done so. This call is valid during a
   * full effort check in TheoryEngine, or after TheoryEngine has terminated
   * with "sat". This means that theories can query this during FULL or
   * LAST_CALL efforts, through the Valuation class.
   */
  bool isRelevant(Node lit);
  /**
   * Get the current relevant selection (see above). This computes this set
   * if not already done so. This call is valid during a full effort check in
   * TheoryEngine, or after TheoryEngine has terminated with "sat". This method
   * sets the flag success to false if we failed to compute relevant
   * assertions, which occurs if the values from the SAT solver do not satisfy
   * the assertions we are notified of. This should never happen.
   *
   * The value of this return is only valid if success was not updated to false.
   */
  const std::unordered_set<TNode>& getRelevantAssertions(bool& success);
  /** Notify lemma, for difficulty measurements */
  void notifyLemma(Node n);
  /** Notify that m is a (candidate) model, for difficulty measurements */
  void notifyCandidateModel(TheoryModel* m);
  /**
   * Get difficulty map
   */
  void getDifficultyMap(std::map<Node, Node>& dmap);

 private:
  /**
   * Add the set of assertions to the formulas known to this class. This
   * method handles optimizations such as breaking apart top-level applications
   * of and.
   */
  void addAssertionsInternal(std::vector<Node>& toProcess);
  /** compute the relevant selection */
  void computeRelevance();
  /**
   * Justify formula n. To "justify" means we have added literals to our
   * relevant selection set (d_rset) whose current values ensure that n
   * evaluates to true or false.
   *
   * This method returns 1 if we justified n to be true, -1 means
   * justified n to be false, 0 means n could not be justified.
   */
  int justify(TNode n, std::unordered_map<TNode, int>& cache);
  /** Is the top symbol of cur a Boolean connective? */
  bool isBooleanConnective(TNode cur);
  /**
   * Update justify last child. This method is a helper function for justify,
   * which is called at the moment that Boolean connective formula cur
   * has a new child that has been computed in the justify cache.
   *
   * @param cur The Boolean connective formula
   * @param childrenJustify The values of the previous children (not including
   * the current one)
   * @param cache The justify cache
   * @return True if we wish to visit the next child. If this is the case, then
   * the justify value of the current child is added to childrenJustify.
   */
  bool updateJustifyLastChild(TNode cur,
                              std::vector<int>& childrenJustify,
                              std::unordered_map<TNode, int>& cache);
  /** The valuation object, used to query current value of theory literals */
  Valuation d_val;
  /** The input assertions */
  NodeList d_input;
  /** The current relevant selection. */
  std::unordered_set<TNode> d_rset;
  /** Have we computed the relevant selection this round? */
  bool d_computed;
  /** Are we in a full effort check? */
  bool d_inFullEffortCheck;
  /**
   * Did we succeed in computing the relevant selection? If this is false, there
   * was a syncronization issue between the input formula and the satisfying
   * assignment since this class found that the input formula was not satisfied
   * by the assignment. This should never happen, but if it does, this class
   * aborts and indicates that all literals are relevant.
   */
  bool d_success;
  /** Are we tracking the sources of why a literal is relevant */
  bool d_trackRSetExp;
  /**
   * Whether we have miniscoped top-level AND of assertions, which is done
   * as an optimization. This is disabled if e.g. we are computing difficulty,
   * which requires preserving the original form of the preprocessed
   * assertions.
   */
  bool d_miniscopeTopLevel;
  /**
   * Map from the domain of d_rset to the assertion in d_input that is the
   * reason why that literal is currently relevant.
   */
  std::map<TNode, TNode> d_rsetExp;
  /** Difficulty module */
  std::unique_ptr<DifficultyManager> d_dman;
};

}  // namespace theory
}  // namespace cvc5

#endif /* CVC5__THEORY__RELEVANCE_MANAGER__H */
