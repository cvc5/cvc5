/******************************************************************************
 * Top contributors (to current version):
 *   Kshitij Bansal, Gereon Kremer, Andres Noetzli
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Justification heuristic for decision making
 *
 * A ATGP-inspired justification-based decision heuristic. See
 * [insert reference] for more details. This code is, or not, based
 * on the CVC3 implementation of the same heuristic.
 *
 * It needs access to the simplified but non-clausal formula.
 */

#include "cvc5_private.h"

#ifndef CVC5__DECISION__JUSTIFICATION_HEURISTIC
#define CVC5__DECISION__JUSTIFICATION_HEURISTIC

#include <unordered_set>
#include <utility>

#include "context/cdhashmap.h"
#include "context/cdhashset.h"
#include "context/cdlist.h"
#include "context/cdo.h"
#include "decision/decision_strategy.h"
#include "expr/node.h"
#include "options/decision_weight.h"
#include "prop/sat_solver_types.h"
#include "util/statistics_stats.h"

namespace cvc5 {
namespace decision {

class JustificationHeuristic : public ITEDecisionStrategy {
  //                   TRUE           FALSE         MEH
  enum SearchResult {FOUND_SPLITTER, NO_SPLITTER, DONT_KNOW};

  typedef std::vector<std::pair<Node, Node> > SkolemList;
  typedef context::CDHashMap<Node, SkolemList, NodeHashFunction> SkolemCache;
  typedef std::vector<Node> ChildList;
  typedef context::
      CDHashMap<Node, std::pair<ChildList, ChildList>, NodeHashFunction>
          ChildCache;
  typedef context::CDHashMap<Node,Node,NodeHashFunction> SkolemMap;
  typedef context::CDHashMap<Node,
                             std::pair<DecisionWeight, DecisionWeight>,
                             NodeHashFunction>
      WeightCache;

  // being 'justified' is monotonic with respect to decisions
  typedef context::CDHashSet<Node,NodeHashFunction> JustifiedSet;
  JustifiedSet d_justified;
  typedef context::CDHashMap<Node,DecisionWeight,NodeHashFunction> ExploredThreshold;
  ExploredThreshold d_exploredThreshold;
  context::CDO<unsigned>  d_prvsIndex;
  context::CDO<unsigned>  d_threshPrvsIndex;

  IntStat d_helpfulness;
  IntStat d_giveup;
  TimerStat d_timestat;

  /**
   * A copy of the assertions that need to be justified
   * directly. Doesn't have ones introduced during during term removal.
   */
  context::CDList<Node> d_assertions;

  /** map from skolems introduced in term removal to the corresponding assertion
   */
  SkolemMap d_skolemAssertions;
  
  /** Cache for skolems present in a atomic formula */
  SkolemCache d_skolemCache;

  /**
   * This is used to prevent infinite loop when trying to find a
   * splitter. Can happen when exploring assertion corresponding to a
   * term-ITE.
   */
  std::unordered_set<Node,NodeHashFunction> d_visited;

  /**
   * Set to track visited nodes in a dfs search done in computeSkolems
   * function
   */
  std::unordered_set<Node, NodeHashFunction> d_visitedComputeSkolems;

  /** current decision for the recursive call */
  prop::SatLiteral d_curDecision;
  /** current threshold for the recursive call */
  DecisionWeight d_curThreshold;

  /** child cache */
  ChildCache d_childCache;

  /** computed polarized weight cache */
  WeightCache d_weightCache;


  class myCompareClass {
    JustificationHeuristic* d_jh;
    bool d_b;
  public:
    myCompareClass(JustificationHeuristic* jh, bool b):d_jh(jh),d_b(b) {};
    bool operator() (TNode n1, TNode n2) {
      return d_jh->getWeightPolarized(n1, d_b) < d_jh->getWeightPolarized(n2, d_b);
    }
  };

public:
 JustificationHeuristic(DecisionEngineOld* de,
                        context::UserContext* uc,
                        context::Context* c);

 ~JustificationHeuristic();

 prop::SatLiteral getNext(bool& stopSearch) override;

 /**
  * Notify this class that assertion is an (input) assertion, not corresponding
  * to a skolem definition.
  */
 void addAssertion(TNode assertion) override;
 /**
  * Notify this class  that lem is the skolem definition for skolem, which is
  * a part of the current assertions.
  */
 void addSkolemDefinition(TNode lem, TNode skolem) override;

private:
 /* getNext with an option to specify threshold */
 prop::SatLiteral getNextThresh(bool& stopSearch, DecisionWeight threshold);

 prop::SatLiteral findSplitter(TNode node, prop::SatValue desiredVal);

 /**
  * Do all the hard work.
  */
 SearchResult findSplitterRec(TNode node, prop::SatValue value);

 /* Helper functions */
 void setJustified(TNode);
 bool checkJustified(TNode);
 DecisionWeight getExploredThreshold(TNode);
 void setExploredThreshold(TNode);
 void setPrvsIndex(int);
 int getPrvsIndex();
 DecisionWeight getWeightPolarized(TNode n, bool polarity);
 DecisionWeight getWeightPolarized(TNode n, prop::SatValue);
 static DecisionWeight getWeight(TNode);
 bool compareByWeightFalse(TNode, TNode);
 bool compareByWeightTrue(TNode, TNode);
 TNode getChildByWeight(TNode n, int i, bool polarity);

 /* If literal exists corresponding to the node return
    that. Otherwise an UNKNOWN */
 prop::SatValue tryGetSatValue(Node n);

 /* Get list of all term-ITEs for the atomic formula v */
 JustificationHeuristic::SkolemList getSkolems(TNode n);

 /**
  * For big and/or nodes, a cache to save starting index into children
  * for efficiently.
  */
 typedef context::CDHashMap<Node, int, NodeHashFunction> StartIndexCache;
 StartIndexCache d_startIndexCache;
 int getStartIndex(TNode node);
 void saveStartIndex(TNode node, int val);

 /* Compute all term-removal skolems in a node recursively */
 void computeSkolems(TNode n, SkolemList& l);

 SearchResult handleAndOrEasy(TNode node, prop::SatValue desiredVal);
 SearchResult handleAndOrHard(TNode node, prop::SatValue desiredVal);
 SearchResult handleBinaryEasy(TNode node1,
                               prop::SatValue desiredVal1,
                               TNode node2,
                               prop::SatValue desiredVal2);
 SearchResult handleBinaryHard(TNode node1,
                               prop::SatValue desiredVal1,
                               TNode node2,
                               prop::SatValue desiredVal2);
 SearchResult handleITE(TNode node, prop::SatValue desiredVal);
 SearchResult handleEmbeddedSkolems(TNode node);
};/* class JustificationHeuristic */

}/* namespace decision */
}  // namespace cvc5

#endif /* CVC5__DECISION__JUSTIFICATION_HEURISTIC */
