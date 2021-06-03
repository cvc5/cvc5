/******************************************************************************
 * Top contributors (to current version):
 *   Kshitij Bansal, Andres Noetzli, Gereon Kremer
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
 * A ATGP-inspired justification-based decision heuristic. This code is based
 * on the CVC3 implementation of the same heuristic -- note below.
 *
 * It needs access to the simplified but non-clausal formula.
 */
#include "justification_heuristic.h"

#include "decision/decision_attributes.h"
#include "decision/decision_engine_old.h"
#include "expr/kind.h"
#include "expr/node_manager.h"
#include "options/decision_options.h"
#include "smt/smt_statistics_registry.h"
#include "smt/term_formula_removal.h"
#include "theory/rewriter.h"
#include "util/random.h"

using namespace cvc5::prop;

namespace cvc5 {
namespace decision {

JustificationHeuristic::JustificationHeuristic(DecisionEngineOld* de,
                                               context::UserContext* uc,
                                               context::Context* c)
    : ITEDecisionStrategy(de, c),
      d_justified(c),
      d_exploredThreshold(c),
      d_prvsIndex(c, 0),
      d_threshPrvsIndex(c, 0),
      d_helpfulness(
          smtStatisticsRegistry().registerInt("decision::jh::helpfulness")),
      d_giveup(smtStatisticsRegistry().registerInt("decision::jh::giveup")),
      d_timestat(smtStatisticsRegistry().registerTimer("decision::jh::time")),
      d_assertions(uc),
      d_skolemAssertions(uc),
      d_skolemCache(uc),
      d_visited(),
      d_visitedComputeSkolems(),
      d_curDecision(),
      d_curThreshold(0),
      d_childCache(uc),
      d_weightCache(uc),
      d_startIndexCache(c)
{
  Trace("decision") << "Justification heuristic enabled" << std::endl;
}

JustificationHeuristic::~JustificationHeuristic() {}

cvc5::prop::SatLiteral JustificationHeuristic::getNext(bool& stopSearch)
{
  if(options::decisionThreshold() > 0) {
    bool stopSearchTmp = false;
    prop::SatLiteral lit =
        getNextThresh(stopSearchTmp, options::decisionThreshold());
    if (lit != prop::undefSatLiteral)
    {
      Assert(stopSearchTmp == false);
      return lit;
    }
    Assert(stopSearchTmp == true);
  }
  return getNextThresh(stopSearch, 0);
}

cvc5::prop::SatLiteral JustificationHeuristic::getNextThresh(
    bool& stopSearch, DecisionWeight threshold)
{
  Trace("decision") << "JustificationHeuristic::getNextThresh(stopSearch, "<<threshold<<")" << std::endl;
  TimerStat::CodeTimer codeTimer(d_timestat);

  d_visited.clear();
  d_curThreshold = threshold;

  if(Trace.isOn("justified")) {
    for(JustifiedSet::key_iterator i = d_justified.key_begin();
        i != d_justified.key_end(); ++i) {
      TNode n = *i;
      prop::SatLiteral l = d_decisionEngine->hasSatLiteral(n)
                               ? d_decisionEngine->getSatLiteral(n)
                               : -1;
      prop::SatValue v = tryGetSatValue(n);
      Trace("justified") <<"{ "<<l<<"}" << n <<": "<<v << std::endl;
    }
  }

  for(unsigned i = getPrvsIndex(); i < d_assertions.size(); ++i) {
    Debug("decision") << "---" << std::endl << d_assertions[i] << std::endl;

    // Sanity check: if it was false, aren't we inconsistent?
    // Commenting out. See bug 374. In short, to do with how CNF stream works.
    // Assert( tryGetSatValue(d_assertions[i]) != SAT_VALUE_FALSE);

    prop::SatValue desiredVal = prop::SAT_VALUE_TRUE;
    prop::SatLiteral litDecision;

    litDecision = findSplitter(d_assertions[i], desiredVal);

    if (litDecision != prop::undefSatLiteral)
    {
      setPrvsIndex(i);
      Trace("decision") << "jh: splitting on " << litDecision << std::endl;
      ++d_helpfulness;
      return litDecision;
    }
  }

  Trace("decision") << "jh: Nothing to split on " << std::endl;

#if defined CVC5_DEBUG
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
  if (d_curThreshold == 0) d_decisionEngine->setResult(prop::SAT_VALUE_TRUE);
  return prop::undefSatLiteral;
}

inline void computeXorIffDesiredValues(Kind k,
                                       prop::SatValue desiredVal,
                                       prop::SatValue& desiredVal1,
                                       prop::SatValue& desiredVal2)
{
  Assert(k == kind::EQUAL || k == kind::XOR);

  bool shouldInvert =
      (desiredVal == prop::SAT_VALUE_TRUE && k == kind::EQUAL)
      || (desiredVal == prop::SAT_VALUE_FALSE && k == kind::XOR);

  if (desiredVal1 == prop::SAT_VALUE_UNKNOWN
      && desiredVal2 == prop::SAT_VALUE_UNKNOWN)
  {
    // CHOICE: pick one of them arbitarily
    desiredVal1 = prop::SAT_VALUE_FALSE;
  }

  if(desiredVal2 == SAT_VALUE_UNKNOWN) {
    desiredVal2 = shouldInvert ? invertValue(desiredVal1) : desiredVal1;
  } else if(desiredVal1 == SAT_VALUE_UNKNOWN) {
    desiredVal1 = shouldInvert ? invertValue(desiredVal2) : desiredVal2;
  }
}

void JustificationHeuristic::addAssertion(TNode assertion)
{
  // Save all assertions locally, including the assertions generated by term
  // removal. We have to make sure that we assign a value to all the Boolean
  // term variables. To illustrate why this is, consider the case where we have
  // a single assertion
  //
  // (or (f a) (f b))
  //
  // where `f` is a function `Bool -> Bool`. Given an assignment:
  //
  // (f a) -> true
  // (f b) -> false
  // a -> false
  //
  // UF will not complain and the justification heuristic considers the
  // assertion to be satisifed. However, we also have to make sure that we pick
  // a value for `b` that is not in conflict with the other assignments (we can
  // only choose `b` to be `true` otherwise the model is incorrect).
  d_assertions.push_back(assertion);
}

void JustificationHeuristic::addSkolemDefinition(TNode lem, TNode skolem)
{
  Trace("decision::jh::ite")
      << " jh-ite: " << skolem << " maps to " << lem << std::endl;
  d_skolemAssertions[skolem] = lem;
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
  return d_exploredThreshold.find(n) == d_exploredThreshold.end()
             ? std::numeric_limits<DecisionWeight>::max()
             : d_exploredThreshold[n];
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
        dW1 = std::numeric_limits<DecisionWeight>::max(), dW2 = 0;
        for(TNode::iterator i=n.begin(); i != n.end(); ++i) {
          dW1 = std::min(dW1, getWeightPolarized(*i, true));
          dW2 = std::max(dW2, getWeightPolarized(*i, false));
        }
      } else if(k == kind::AND) {
        dW1 = 0, dW2 = std::numeric_limits<DecisionWeight>::max();
        for(TNode::iterator i=n.begin(); i != n.end(); ++i) {
          dW1 = std::max(dW1, getWeightPolarized(*i, true));
          dW2 = std::min(dW2, getWeightPolarized(*i, false));
        }
      } else if(k == kind::IMPLIES) {
        dW1 = std::min(getWeightPolarized(n[0], false),
                       getWeightPolarized(n[1], true));
        dW2 = std::max(getWeightPolarized(n[0], true),
                       getWeightPolarized(n[1], false));
      } else if(k == kind::NOT) {
        dW1 = getWeightPolarized(n[0], false);
        dW2 = getWeightPolarized(n[0], true);
      } else {
        dW1 = 0;
        for(TNode::iterator i=n.begin(); i != n.end(); ++i) {
          dW1 = std::max(dW1, getWeightPolarized(*i, true));
          dW1 = std::max(dW1, getWeightPolarized(*i, false));
        }
        dW2 = dW1;
      }

    }
    d_weightCache[n] = std::make_pair(dW1, dW2);
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
        dW = std::max(dW, getWeight(*i));
      n.setAttribute(DecisionWeightAttr(), dW);
    }
    else if (combiningFn == options::DecisionWeightInternal::SUM
             || combiningFn == options::DecisionWeightInternal::USR1)
    {
      DecisionWeight dW = 0;
      for (TNode::iterator i = n.begin(); i != n.end(); ++i)
        dW = std::max(dW, getWeight(*i));
      n.setAttribute(DecisionWeightAttr(), dW);
    }
    else
    {
      Unreachable();
    }
  }
  return n.getAttribute(DecisionWeightAttr());
}

typedef std::vector<TNode> ChildList;
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

JustificationHeuristic::SkolemList JustificationHeuristic::getSkolems(TNode n)
{
  SkolemCache::iterator it = d_skolemCache.find(n);
  if (it != d_skolemCache.end())
  {
    return (*it).second;
  }
  else
  {
    // Compute the list of Skolems
    // TODO: optimize by avoiding multiple lookup for d_skolemCache[n]
    d_visitedComputeSkolems.clear();
    SkolemList ilist;
    computeSkolems(n, ilist);
    d_skolemCache.insert(n, ilist);
    return ilist;
  }
}

void JustificationHeuristic::computeSkolems(TNode n, SkolemList& l)
{
  Trace("decision::jh::skolems") << " computeSkolems( " << n << ", &l)\n";
  d_visitedComputeSkolems.insert(n);
  for(unsigned i=0; i<n.getNumChildren(); ++i) {
    SkolemMap::iterator it2 = d_skolemAssertions.find(n[i]);
    if (it2 != d_skolemAssertions.end())
    {
      l.push_back(std::make_pair(n[i], (*it2).second));
      Assert(n[i].getNumChildren() == 0);
    }
    if (d_visitedComputeSkolems.find(n[i]) == d_visitedComputeSkolems.end())
    {
      computeSkolems(n[i], l);
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

#if defined CVC5_ASSERTIONS || defined CVC5_DEBUG
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
    // if node has embedded skolems due to term removal, resolve that first
    if (handleEmbeddedSkolems(node) == FOUND_SPLITTER) return FOUND_SPLITTER;

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
    std::swap(node1, node2);
    std::swap(desiredVal1, desiredVal2);
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
    std::swap(node1, node2);
    std::swap(desiredVal1, desiredVal2);
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

JustificationHeuristic::SearchResult
JustificationHeuristic::handleEmbeddedSkolems(TNode node)
{
  const SkolemList l = getSkolems(node);
  Trace("decision::jh::skolems") << " skolems size = " << l.size() << std::endl;

  bool noSplitter = true;
  for (SkolemList::const_iterator i = l.begin(); i != l.end(); ++i)
  {
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

} /* namespace decision */
}  // namespace cvc5
