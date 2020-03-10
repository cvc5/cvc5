/*********************                                                        */
/*! \file justification_heuristic.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Kshitij Bansal, Aina Niemetz, Tim King
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Justification heuristic for decision making
 **
 ** A ATGP-inspired justification-based decision heuristic. This code is based
 ** on the CVC3 implementation of the same heuristic -- note below.
 **
 ** It needs access to the simplified but non-clausal formula.
 **/
#include "justification_heuristic.h"

#include "expr/kind.h"
#include "expr/node_manager.h"
#include "options/decision_options.h"
#include "theory/rewriter.h"
#include "smt/term_formula_removal.h"
#include "smt/smt_statistics_registry.h"
#include "util/random.h"

namespace CVC4 {

JustificationHeuristic::JustificationHeuristic(CVC4::DecisionEngine* de,
                                               context::UserContext* uc,
                                               context::Context* c)
    : ITEDecisionStrategy(de, c),
      d_justified(c),
      d_exploredThreshold(c),
      d_prvsIndex(c, 0),
      d_threshPrvsIndex(c, 0),
      d_helpfulness("decision::jh::helpfulness", 0),
      d_giveup("decision::jh::giveup", 0),
      d_timestat("decision::jh::time"),
      d_assertions(uc),
      d_iteAssertions(uc),
      d_iteCache(uc),
      d_visited(),
      d_visitedComputeITE(),
      d_curDecision(),
      d_curThreshold(0),
      d_childCache(uc),
      d_weightCache(uc),
      d_startIndexCache(c)
{
  smtStatisticsRegistry()->registerStat(&d_helpfulness);
  smtStatisticsRegistry()->registerStat(&d_giveup);
  smtStatisticsRegistry()->registerStat(&d_timestat);
  Trace("decision") << "Justification heuristic enabled" << std::endl;
}

JustificationHeuristic::~JustificationHeuristic()
{
  smtStatisticsRegistry()->unregisterStat(&d_helpfulness);
  smtStatisticsRegistry()->unregisterStat(&d_giveup);
  smtStatisticsRegistry()->unregisterStat(&d_timestat);
}

CVC4::prop::SatLiteral JustificationHeuristic::getNext(bool &stopSearch)
{
  if(options::decisionThreshold() > 0) {
    bool stopSearchTmp = false;
    SatLiteral lit = getNextThresh(stopSearchTmp, options::decisionThreshold());
    if(lit != undefSatLiteral) {
      Assert(stopSearchTmp == false);
      return lit;
    }
    Assert(stopSearchTmp == true);
  }
  return getNextThresh(stopSearch, 0);
}

CVC4::prop::SatLiteral JustificationHeuristic::getNextThresh(bool &stopSearch, DecisionWeight threshold) {
  Trace("decision") << "JustificationHeuristic::getNextThresh(stopSearch, "<<threshold<<")" << std::endl;
  TimerStat::CodeTimer codeTimer(d_timestat);

  d_visited.clear();
  d_curThreshold = threshold;

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

  for(unsigned i = getPrvsIndex(); i < d_assertions.size(); ++i) {
    Debug("decision") << "---" << std::endl << d_assertions[i] << std::endl;

    // Sanity check: if it was false, aren't we inconsistent?
    // Commenting out. See bug 374. In short, to do with how CNF stream works.
    // Assert( tryGetSatValue(d_assertions[i]) != SAT_VALUE_FALSE);

    SatValue desiredVal = SAT_VALUE_TRUE;
    SatLiteral litDecision;

    litDecision = findSplitter(d_assertions[i], desiredVal);

    if(litDecision != undefSatLiteral) {
      setPrvsIndex(i);
      Trace("decision") << "jh: splitting on " << litDecision << std::endl;
      ++d_helpfulness;
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
  Assert(alljustified || d_curThreshold != 0);
#endif

  // SAT solver can stop...
  stopSearch = true;
  if(d_curThreshold == 0)
    d_decisionEngine->setResult(SAT_VALUE_TRUE);
  return prop::undefSatLiteral;
}


inline void computeXorIffDesiredValues
(Kind k, SatValue desiredVal, SatValue &desiredVal1, SatValue &desiredVal2)
{
  Assert(k == kind::EQUAL || k == kind::XOR);

  bool shouldInvert =
    (desiredVal == SAT_VALUE_TRUE && k == kind::EQUAL) ||
    (desiredVal == SAT_VALUE_FALSE && k == kind::XOR);

  if(desiredVal1 == SAT_VALUE_UNKNOWN &&
     desiredVal2 == SAT_VALUE_UNKNOWN) {
    // CHOICE: pick one of them arbitarily
    desiredVal1 = SAT_VALUE_FALSE;
  }

  if(desiredVal2 == SAT_VALUE_UNKNOWN) {
    desiredVal2 = shouldInvert ? invertValue(desiredVal1) : desiredVal1;
  } else if(desiredVal1 == SAT_VALUE_UNKNOWN) {
    desiredVal1 = shouldInvert ? invertValue(desiredVal2) : desiredVal2;
  }
}

void JustificationHeuristic::addAssertions(
    const preprocessing::AssertionPipeline &assertions)
{
  size_t assertionsEnd = assertions.getRealAssertionsEnd();

  Trace("decision")
    << "JustificationHeuristic::addAssertions()"
    << " size = " << assertions.size()
    << " assertionsEnd = " << assertionsEnd
    << std::endl;

  // Save the 'real' assertions locally
  for (size_t i = 0; i < assertionsEnd; i++)
  {
    d_assertions.push_back(assertions[i]);
  }

  // Save mapping between ite skolems and ite assertions
  for (const std::pair<const Node, unsigned> &i : assertions.getIteSkolemMap())
  {
    Trace("decision::jh::ite") << " jh-ite: " << (i.first) << " maps to "
                               << assertions[(i.second)] << std::endl;
    Assert(i.second >= assertionsEnd && i.second < assertions.size());

    d_iteAssertions[i.first] = assertions[i.second];
  }

  // Automatic weight computation
}

SatLiteral JustificationHeuristic::findSplitter(TNode node,
                                                SatValue desiredVal)
{
  d_curDecision = undefSatLiteral;
  findSplitterRec(node, desiredVal);
  return d_curDecision;
}


void JustificationHeuristic::setJustified(TNode n)
{
  d_justified.insert(n);
}

bool JustificationHeuristic::checkJustified(TNode n)
{
  return d_justified.find(n) != d_justified.end();
}

DecisionWeight JustificationHeuristic::getExploredThreshold(TNode n)
{
  return
    d_exploredThreshold.find(n) == d_exploredThreshold.end() ?
    numeric_limits<DecisionWeight>::max() : d_exploredThreshold[n];
}

void JustificationHeuristic::setExploredThreshold(TNode n)
{
  d_exploredThreshold[n] = d_curThreshold;
}

int JustificationHeuristic::getPrvsIndex()
{
  if(d_curThreshold == 0)
    return d_prvsIndex;
  else
    return d_threshPrvsIndex;
}

void JustificationHeuristic::setPrvsIndex(int prvsIndex)
{
  if(d_curThreshold == 0)
    d_prvsIndex = prvsIndex;
  else
    d_threshPrvsIndex = prvsIndex;
}

DecisionWeight JustificationHeuristic::getWeightPolarized(TNode n, SatValue satValue)
{
  Assert(satValue == SAT_VALUE_TRUE || satValue == SAT_VALUE_FALSE);
  return getWeightPolarized(n, satValue == SAT_VALUE_TRUE);
}

DecisionWeight JustificationHeuristic::getWeightPolarized(TNode n, bool polarity)
{
  if (options::decisionWeightInternal()
      != options::DecisionWeightInternal::USR1)
  {
    return getWeight(n);
  }

  if(d_weightCache.find(n) == d_weightCache.end()) {
    Kind k = n.getKind();
    theory::TheoryId tId  = theory::kindToTheoryId(k);
    DecisionWeight dW1, dW2;
    if(tId != theory::THEORY_BOOL) {
      dW1 = dW2 = getWeight(n);
    } else {

      if(k == kind::OR) {
        dW1 = numeric_limits<DecisionWeight>::max(), dW2 = 0;
        for(TNode::iterator i=n.begin(); i != n.end(); ++i) {
          dW1 = min(dW1, getWeightPolarized(*i, true));
          dW2 = max(dW2, getWeightPolarized(*i, false));
        }
      } else if(k == kind::AND) {
        dW1 = 0, dW2 = numeric_limits<DecisionWeight>::max();
        for(TNode::iterator i=n.begin(); i != n.end(); ++i) {
          dW1 = max(dW1, getWeightPolarized(*i, true));
          dW2 = min(dW2, getWeightPolarized(*i, false));
        }
      } else if(k == kind::IMPLIES) {
        dW1 = min(getWeightPolarized(n[0], false),
                  getWeightPolarized(n[1], true));
        dW2 = max(getWeightPolarized(n[0], true),
                  getWeightPolarized(n[1], false));
      } else if(k == kind::NOT) {
        dW1 = getWeightPolarized(n[0], false);
        dW2 = getWeightPolarized(n[0], true);
      } else {
        dW1 = 0;
        for(TNode::iterator i=n.begin(); i != n.end(); ++i) {
          dW1 = max(dW1, getWeightPolarized(*i, true));
          dW1 = max(dW1, getWeightPolarized(*i, false));
        }
        dW2 = dW1;
      }

    }
    d_weightCache[n] = make_pair(dW1, dW2);
  }
  return polarity ? d_weightCache[n].get().first : d_weightCache[n].get().second;
}

DecisionWeight JustificationHeuristic::getWeight(TNode n) {
  if(!n.hasAttribute(DecisionWeightAttr()) ) {
    options::DecisionWeightInternal combiningFn =
        options::decisionWeightInternal();

    if (combiningFn == options::DecisionWeightInternal::OFF
        || n.getNumChildren() == 0)
    {
      if (options::decisionRandomWeight() != 0)
      {
        n.setAttribute(DecisionWeightAttr(),
            Random::getRandom().pick(0, options::decisionRandomWeight()-1));
      }
    }
    else if (combiningFn == options::DecisionWeightInternal::MAX)
    {
      DecisionWeight dW = 0;
      for (TNode::iterator i = n.begin(); i != n.end(); ++i)
        dW = max(dW, getWeight(*i));
      n.setAttribute(DecisionWeightAttr(), dW);
    }
    else if (combiningFn == options::DecisionWeightInternal::SUM
             || combiningFn == options::DecisionWeightInternal::USR1)
    {
      DecisionWeight dW = 0;
      for (TNode::iterator i = n.begin(); i != n.end(); ++i)
        dW = max(dW, getWeight(*i));
      n.setAttribute(DecisionWeightAttr(), dW);
    }
    else
    {
      Unreachable();
    }
  }
  return n.getAttribute(DecisionWeightAttr());
}

typedef vector<TNode> ChildList;
TNode JustificationHeuristic::getChildByWeight(TNode n, int i, bool polarity) {
  if(options::decisionUseWeight()) {
    // TODO: Optimize storing & access
    if(d_childCache.find(n) == d_childCache.end()) {
      ChildList list0(n.begin(), n.end()), list1(n.begin(), n.end());
      std::sort(list0.begin(), list0.end(), JustificationHeuristic::myCompareClass(this,false));
      std::sort(list1.begin(), list1.end(), JustificationHeuristic::myCompareClass(this,true));
      d_childCache[n] = make_pair(list0, list1);
    }
    return polarity ? d_childCache[n].get().second[i] : d_childCache[n].get().first[i];
  } else {
    return n[i];
  }
}

SatValue JustificationHeuristic::tryGetSatValue(Node n)
{
  Debug("decision") << "   "  << n << " has sat value " << " ";
  if(d_decisionEngine->hasSatLiteral(n) ) {
    Debug("decision") << d_decisionEngine->getSatValue(n) << std::endl;
    return d_decisionEngine->getSatValue(n);
  } else {
    Debug("decision") << "NO SAT LITERAL" << std::endl;
    return SAT_VALUE_UNKNOWN;
  }//end of else
}

JustificationHeuristic::IteList
JustificationHeuristic::getITEs(TNode n)
{
  IteCache::iterator it = d_iteCache.find(n);
  if(it != d_iteCache.end()) {
    return (*it).second;
  } else {
    // Compute the list of ITEs
    // TODO: optimize by avoiding multiple lookup for d_iteCache[n]
    d_visitedComputeITE.clear();
    IteList ilist;
    computeITEs(n, ilist);
    d_iteCache.insert(n, ilist);
    return ilist;
  }
}

void JustificationHeuristic::computeITEs(TNode n, IteList &l)
{
  Trace("decision::jh::ite") << " computeITEs( " << n << ", &l)\n";
  d_visitedComputeITE.insert(n);
  for(unsigned i=0; i<n.getNumChildren(); ++i) {
    SkolemMap::iterator it2 = d_iteAssertions.find(n[i]);
    if(it2 != d_iteAssertions.end()) {
      l.push_back(make_pair(n[i], (*it2).second));
      Assert(n[i].getNumChildren() == 0);
    }
    if(d_visitedComputeITE.find(n[i]) ==
         d_visitedComputeITE.end()) {
      computeITEs(n[i], l);
    }
  }
}

JustificationHeuristic::SearchResult
JustificationHeuristic::findSplitterRec(TNode node, SatValue desiredVal)
{
  /**
   * Main idea
   *
   * Given a boolean formula "node", the goal is to try to make it
   * evaluate to "desiredVal" (true/false). for instance if "node" is a OR
   * formula we want to make it evaluate to true, we'd like one of the
   * children to be true. this is done recursively.
   */

  Trace("decision::jh")
    << "findSplitterRec(" << node << ", "
    << desiredVal << ", .. )" << std::endl;

  /* Handle NOT as a special case */
  while (node.getKind() == kind::NOT) {
    desiredVal = invertValue(desiredVal);
    node = node[0];
  }

  /* Base case */
  if (checkJustified(node)) {
    Debug("decision::jh") << "  justified, returning" << std::endl;
    return NO_SPLITTER;
  }
  if (getExploredThreshold(node) < d_curThreshold) {
    Debug("decision::jh") << "  explored, returning" << std::endl;
    Assert(d_curThreshold != 0);
    return DONT_KNOW;
  }

#if defined CVC4_ASSERTIONS || defined CVC4_DEBUG
  // We don't always have a sat literal, so remember that. Will need
  // it for some assertions we make.
  bool litPresent = d_decisionEngine->hasSatLiteral(node);
  if(Debug.isOn("decision")) {
    if(!litPresent) {
      Debug("decision") << "no sat literal for this node" << std::endl;
    }
  }
#endif

  // Get value of sat literal for the node, if there is one
  SatValue litVal = tryGetSatValue(node);

  /* You'd better know what you want */
  Assert(desiredVal != SAT_VALUE_UNKNOWN) << "expected known value";

  /* Good luck, hope you can get what you want */
  // See bug 374
  // Assert(litVal == desiredVal || litVal == SAT_VALUE_UNKNOWN) <<
  //       "invariant violated";

  /* What type of node is this */
  Kind k = node.getKind();
  theory::TheoryId tId = theory::kindToTheoryId(k);
  bool isAtom =
     (k == kind::BOOLEAN_TERM_VARIABLE ) ||
     ( (tId != theory::THEORY_BOOL) &&
       (k != kind::EQUAL || (!node[0].getType().isBoolean())) );

  /* Some debugging stuff */
  Debug("decision::jh") << "kind = " << k << std::endl
                        << "theoryId = " << tId << std::endl
                        << "node = " << node << std::endl
                        << "litVal = " << litVal << std::endl;

  /**
   * If not in theory of booleans, check if this is something to split-on.
   */
  if(isAtom) {
    // if node has embedded ites, resolve that first
    if(handleEmbeddedITEs(node) == FOUND_SPLITTER)
      return FOUND_SPLITTER;

    if(litVal != SAT_VALUE_UNKNOWN) {
      Assert(litVal == desiredVal);
      setJustified(node);
      return NO_SPLITTER;
    }
    else {
      Assert(d_decisionEngine->hasSatLiteral(node));
      if(d_curThreshold != 0 && getWeightPolarized(node, desiredVal) >= d_curThreshold)
        return DONT_KNOW;
      SatVariable v =
        d_decisionEngine->getSatLiteral(node).getSatVariable();
      d_curDecision = SatLiteral(v, /* negated = */ desiredVal != SAT_VALUE_TRUE );
      Trace("decision-node") << "[decision-node] requesting split on " << d_curDecision
                             << ", node: " << node
                             << ", polarity: " << (desiredVal == SAT_VALUE_TRUE ? "true" : "false") << std::endl;
      return FOUND_SPLITTER;
    }
  }

  SearchResult ret = NO_SPLITTER;
  switch (k) {

  case kind::CONST_BOOLEAN:
    Assert(node.getConst<bool>() == false || desiredVal == SAT_VALUE_TRUE);
    Assert(node.getConst<bool>() == true || desiredVal == SAT_VALUE_FALSE);
    break;

  case kind::AND:
    if (desiredVal == SAT_VALUE_FALSE)
      ret = handleAndOrEasy(node, desiredVal);
    else
      ret = handleAndOrHard(node, desiredVal);
    break;

  case kind::OR:
    if (desiredVal == SAT_VALUE_FALSE)
      ret = handleAndOrHard(node, desiredVal);
    else
      ret = handleAndOrEasy(node, desiredVal);
    break;

  case kind::IMPLIES:
    if (desiredVal == SAT_VALUE_FALSE)
      ret = handleBinaryHard(node[0], SAT_VALUE_TRUE,
                             node[1], SAT_VALUE_FALSE);

    else
      ret = handleBinaryEasy(node[0], SAT_VALUE_FALSE,
                             node[1], SAT_VALUE_TRUE);
    break;

  case kind::XOR:
  case kind::EQUAL: {
    SatValue desiredVal1 = tryGetSatValue(node[0]);
    SatValue desiredVal2 = tryGetSatValue(node[1]);
    computeXorIffDesiredValues(k, desiredVal, desiredVal1, desiredVal2);
    ret = handleBinaryHard(node[0], desiredVal1,
                           node[1], desiredVal2);
    break;
  }

  case kind::ITE:
    ret = handleITE(node, desiredVal);
    break;

  default: Assert(false) << "Unexpected Boolean operator"; break;
  }//end of switch(k)

  if(ret == DONT_KNOW) {
    setExploredThreshold(node);
  }

  if(ret == NO_SPLITTER) {
    Assert(litPresent == false || litVal == desiredVal)
        << "Output should be justified";
    setJustified(node);
  }
  return ret;
}/* findRecSplit method */

JustificationHeuristic::SearchResult
JustificationHeuristic::handleAndOrEasy(TNode node, SatValue desiredVal)
{
  Assert((node.getKind() == kind::AND and desiredVal == SAT_VALUE_FALSE)
         or (node.getKind() == kind::OR and desiredVal == SAT_VALUE_TRUE));

  int numChildren = node.getNumChildren();
  SatValue desiredValInverted = invertValue(desiredVal);
  for(int i = 0; i < numChildren; ++i) {
    TNode curNode = getChildByWeight(node, i, desiredVal);
    if ( tryGetSatValue(curNode) != desiredValInverted ) {
      SearchResult ret = findSplitterRec(curNode, desiredVal);
      if(ret != DONT_KNOW) {
        return ret;
      }
    }
  }
  Assert(d_curThreshold != 0) << "handleAndOrEasy: No controlling input found";
  return DONT_KNOW;
}

int JustificationHeuristic::getStartIndex(TNode node) {
  return d_startIndexCache[node];
}
void JustificationHeuristic::saveStartIndex(TNode node, int val) {
  d_startIndexCache[node] = val;
}

JustificationHeuristic::SearchResult JustificationHeuristic::handleAndOrHard(TNode node,
                                             SatValue desiredVal) {
  Assert((node.getKind() == kind::AND and desiredVal == SAT_VALUE_TRUE)
         or (node.getKind() == kind::OR and desiredVal == SAT_VALUE_FALSE));

  int numChildren = node.getNumChildren();
  bool noSplitter = true;
  int i_st = getStartIndex(node);
  for(int i = i_st; i < numChildren; ++i) {
    TNode curNode = getChildByWeight(node, i, desiredVal);
    SearchResult ret = findSplitterRec(curNode, desiredVal);
    if (ret == FOUND_SPLITTER) {
      if(i != i_st) saveStartIndex(node, i);
      return FOUND_SPLITTER;
    }
    noSplitter = noSplitter && (ret == NO_SPLITTER);
  }
  return noSplitter ? NO_SPLITTER : DONT_KNOW;
}

JustificationHeuristic::SearchResult JustificationHeuristic::handleBinaryEasy(TNode node1,
                                              SatValue desiredVal1,
                                              TNode node2,
                                              SatValue desiredVal2)
{
  if(options::decisionUseWeight() &&
     getWeightPolarized(node1, desiredVal1) > getWeightPolarized(node2, desiredVal2)) {
    swap(node1, node2);
    swap(desiredVal1, desiredVal2);
  }

  if ( tryGetSatValue(node1) != invertValue(desiredVal1) ) {
    SearchResult ret = findSplitterRec(node1, desiredVal1);
    if(ret != DONT_KNOW)
      return ret;
  }
  if ( tryGetSatValue(node2) != invertValue(desiredVal2) ) {
    SearchResult ret = findSplitterRec(node2, desiredVal2);
    if(ret != DONT_KNOW)
      return ret;
  }
  Assert(d_curThreshold != 0) << "handleBinaryEasy: No controlling input found";
  return DONT_KNOW;
}

JustificationHeuristic::SearchResult JustificationHeuristic::handleBinaryHard(TNode node1,
                                              SatValue desiredVal1,
                                              TNode node2,
                                              SatValue desiredVal2)
{
  if(options::decisionUseWeight() &&
     getWeightPolarized(node1, desiredVal1) > getWeightPolarized(node2, desiredVal2)) {
    swap(node1, node2);
    swap(desiredVal1, desiredVal2);
  }

  bool noSplitter = true;
  SearchResult ret;

  ret = findSplitterRec(node1, desiredVal1);
  if (ret == FOUND_SPLITTER)
    return FOUND_SPLITTER;
  noSplitter &= (ret == NO_SPLITTER);

  ret = findSplitterRec(node2, desiredVal2);
  if (ret == FOUND_SPLITTER)
    return FOUND_SPLITTER;
  noSplitter &= (ret == NO_SPLITTER);

  return noSplitter ? NO_SPLITTER : DONT_KNOW;
}

JustificationHeuristic::SearchResult JustificationHeuristic::handleITE(TNode node, SatValue desiredVal)
{
  Debug("decision::jh") << " handleITE (" << node << ", "
                              << desiredVal << std::endl;

  //[0]: if, [1]: then, [2]: else
  SatValue ifVal = tryGetSatValue(node[0]);
  if (ifVal == SAT_VALUE_UNKNOWN) {
    SatValue trueChildVal = tryGetSatValue(node[1]);
    SatValue falseChildVal = tryGetSatValue(node[2]);
    SatValue ifDesiredVal;

    if(trueChildVal == desiredVal || falseChildVal == invertValue(desiredVal)) {
      ifDesiredVal = SAT_VALUE_TRUE;
    } else if(trueChildVal == invertValue(desiredVal) ||
              falseChildVal == desiredVal ||
              (options::decisionUseWeight() &&
               getWeightPolarized(node[1], true) > getWeightPolarized(node[2], false))
              ) {
      ifDesiredVal = SAT_VALUE_FALSE;
    } else {
      ifDesiredVal = SAT_VALUE_TRUE;
    }

    if(findSplitterRec(node[0], ifDesiredVal) == FOUND_SPLITTER)
      return FOUND_SPLITTER;

    Assert(d_curThreshold != 0) << "No controlling input found (6)";
    return DONT_KNOW;
  } else {
    // Try to justify 'if'
    if(findSplitterRec(node[0], ifVal) == FOUND_SPLITTER)
      return FOUND_SPLITTER;

    // If that was successful, we need to go into only one of 'then'
    // or 'else'
    int ch = (ifVal == SAT_VALUE_TRUE) ? 1 : 2;

    if( findSplitterRec(node[ch], desiredVal) == FOUND_SPLITTER ) {
      return FOUND_SPLITTER;
    }

    return NO_SPLITTER;
  }// else (...ifVal...)
}

JustificationHeuristic::SearchResult JustificationHeuristic::handleEmbeddedITEs(TNode node)
{
  const IteList l = getITEs(node);
  Trace("decision::jh::ite") << " ite size = " << l.size() << std::endl;

  bool noSplitter = true;
  for(IteList::const_iterator i = l.begin(); i != l.end(); ++i) {
    if(d_visited.find((*i).first) == d_visited.end()) {
      d_visited.insert((*i).first);
      SearchResult ret = findSplitterRec((*i).second, SAT_VALUE_TRUE);
      if (ret == FOUND_SPLITTER)
        return FOUND_SPLITTER;
      noSplitter = noSplitter && (ret == NO_SPLITTER);
      d_visited.erase((*i).first);
    }
  }
  return noSplitter ? NO_SPLITTER : DONT_KNOW;
}

} /* namespace CVC4 */
