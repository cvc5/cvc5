/*********************                                                        */
/*! \file justification_heuristic.h
 ** \verbatim
 ** Original author: kshitij
 ** Major contributors: none
 ** Minor contributors (to current version): mdeters
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009-2012  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief Justification heuristic for decision making
 **
 ** A ATGP-inspired justification-based decision heuristic. See
 ** [insert reference] for more details. This code is, or not, based
 ** on the CVC3 implementation of the same heuristic.
 **
 ** It needs access to the simplified but non-clausal formula.
 **/

#include "cvc4_private.h"

#ifndef __CVC4__DECISION__JUSTIFICATION_HEURISTIC
#define __CVC4__DECISION__JUSTIFICATION_HEURISTIC

#include "decision_engine.h"
#include "decision_strategy.h"

#include "context/cdhashset.h"
#include "context/cdlist.h"
#include "context/cdhashmap.h"
#include "expr/node.h"
#include "prop/sat_solver_types.h"

namespace CVC4 {

namespace decision {

class GiveUpException : public Exception {
public:
  GiveUpException() : 
    Exception("justification heuristic: giving up") {
  }
};/* class GiveUpException */

class JustificationHeuristic : public ITEDecisionStrategy {
  typedef std::vector<pair<TNode,TNode> > IteList;
  typedef hash_map<TNode,IteList,TNodeHashFunction> IteCache;
  typedef context::CDHashMap<TNode,TNode,TNodeHashFunction> SkolemMap;

  // being 'justified' is monotonic with respect to decisions
  typedef context::CDHashSet<Node,NodeHashFunction> JustifiedSet;
  JustifiedSet d_justified;
  context::CDO<unsigned>  d_prvsIndex;

  IntStat d_helfulness;
  IntStat d_giveup;
  TimerStat d_timestat;

  /**
   * A copy of the assertions that need to be justified
   * directly. Doesn't have ones introduced during during ITE-removal.
   */
  context::CDList<TNode> d_assertions;
  //TNode is fine since decisionEngine has them too

  /** map from ite-rewrite skolem to a boolean-ite assertion */
  SkolemMap d_iteAssertions;
  // 'key' being TNode is fine since if a skolem didn't exist anywhere,
  // we won't look it up. as for 'value', same reason as d_assertions

  /** Cache for ITE skolems present in a atomic formula */
  IteCache d_iteCache;

  /**
   * This is used to prevent infinite loop when trying to find a
   * splitter. Can happen when exploring assertion corresponding to a
   * term-ITE.
   */
  hash_set<TNode,TNodeHashFunction> d_visited;

  /**
   * Set to track visited nodes in a dfs search done in computeITE
   * function
   */
  hash_set<TNode,TNodeHashFunction> d_visitedComputeITE;
public:
  JustificationHeuristic(CVC4::DecisionEngine* de,
                         context::Context *uc,
                         context::Context *c):
    ITEDecisionStrategy(de, c),
    d_justified(c),
    d_prvsIndex(c, 0),
    d_helfulness("decision::jh::helpfulness", 0),
    d_giveup("decision::jh::giveup", 0),
    d_timestat("decision::jh::time"),
    d_assertions(uc),
    d_iteAssertions(uc) {
    StatisticsRegistry::registerStat(&d_helfulness);
    StatisticsRegistry::registerStat(&d_giveup);
    StatisticsRegistry::registerStat(&d_timestat);
    Trace("decision") << "Justification heuristic enabled" << std::endl;
  }
  ~JustificationHeuristic() {
    StatisticsRegistry::unregisterStat(&d_helfulness);
    StatisticsRegistry::unregisterStat(&d_giveup);
    StatisticsRegistry::unregisterStat(&d_timestat);
  }
  prop::SatLiteral getNext(bool &stopSearch) {
    Trace("decision") << "JustificationHeuristic::getNext()" << std::endl;
    TimerStat::CodeTimer codeTimer(d_timestat);

    d_visited.clear();

    if(Trace.isOn("justified")) {
      for(JustifiedSet::key_iterator i = d_justified.key_begin();
          i != d_justified.key_end(); ++i) {
        TNode n = *i;
        SatLiteral l = d_decisionEngine->hasSatLiteral(n) ?
          d_decisionEngine->getSatLiteral(n) : -1;
        SatValue v = tryGetSatValue(n);
        Trace("justified") <<"{ "<<l<<"}" << n <<": "<<v << std::endl;
      }
    }

    for(unsigned i = d_prvsIndex; i < d_assertions.size(); ++i) {
      Debug("decision") << "---" << std::endl << d_assertions[i] << std::endl;

      // Sanity check: if it was false, aren't we inconsistent?
      Assert( tryGetSatValue(d_assertions[i]) != SAT_VALUE_FALSE);

      SatValue desiredVal = SAT_VALUE_TRUE;
      SatLiteral litDecision;
      try {
        litDecision = findSplitter(d_assertions[i], desiredVal);
      }catch(GiveUpException &e) {
        return prop::undefSatLiteral;
      }

      if(litDecision != undefSatLiteral) {
        d_prvsIndex = i;
        return litDecision;
      }
    }

    Trace("decision") << "jh: Nothing to split on " << std::endl;

#if defined CVC4_DEBUG
    bool alljustified = true;
    for(unsigned i = 0 ; i < d_assertions.size() && alljustified ; ++i) {
      TNode curass = d_assertions[i];
      while(curass.getKind() == kind::NOT)
        curass = curass[0];
      alljustified &= checkJustified(curass);

      if(Debug.isOn("decision")) {
	if(!checkJustified(curass))
	  Debug("decision") << "****** Not justified [i="<<i<<"]: " 
                            << d_assertions[i] << std::endl;
      }
    }
    Assert(alljustified);
#endif

    // SAT solver can stop...
    stopSearch = true;
    d_decisionEngine->setResult(SAT_VALUE_TRUE);
    return prop::undefSatLiteral;
  }

  void addAssertions(const std::vector<Node> &assertions,
                     unsigned assertionsEnd,
                     IteSkolemMap iteSkolemMap) {
    Trace("decision")
      << "JustificationHeuristic::addAssertions()" 
      << " size = " << assertions.size()
      << " assertionsEnd = " << assertionsEnd
      << std::endl;

    // Save the 'real' assertions locally
    for(unsigned i = 0; i < assertionsEnd; ++i)
      d_assertions.push_back(assertions[i]);

    // Save mapping between ite skolems and ite assertions
    for(IteSkolemMap::iterator i = iteSkolemMap.begin();
        i != iteSkolemMap.end(); ++i) {
      Trace("jh-ite") << " jh-ite: " << (i->first) << " maps to "
                      << assertions[(i->second)] << std::endl;
      Assert(i->second >= assertionsEnd && i->second < assertions.size());
      d_iteAssertions[i->first] = assertions[i->second];
    }
  }

private:
  SatLiteral findSplitter(TNode node, SatValue desiredVal)
  {
    bool ret;
    SatLiteral litDecision;
    ret = findSplitterRec(node, desiredVal, &litDecision);
    if(ret == true) {
      Debug("decision") << "Yippee!!" << std::endl;
      ++d_helfulness;
      return litDecision;
    } else {
      return undefSatLiteral;
    }
  }
  
  /** 
   * Do all the hard work. 
   */ 
  bool findSplitterRec(TNode node, SatValue value, SatLiteral* litDecision);

  /* Helper functions */
  void setJustified(TNode);
  bool checkJustified(TNode);
  
  /* If literal exists corresponding to the node return
     that. Otherwise an UNKNOWN */
  SatValue tryGetSatValue(Node n);

  /* Get list of all term-ITEs for the atomic formula v */
  const JustificationHeuristic::IteList& getITEs(TNode n);

  /* Compute all term-ITEs in a node recursively */
  void computeITEs(TNode n, IteList &l);
};/* class JustificationHeuristic */

}/* namespace decision */

}/* namespace CVC4 */

#endif /* __CVC4__DECISION__JUSTIFICATION_HEURISTIC */
