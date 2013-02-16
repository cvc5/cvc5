/*********************                                                        */
/*! \file justification_heuristic.cpp
 ** \verbatim
 ** Original author: kshitij
 ** Major contributors: none
 ** Minor contributors (to current version): dejan, mdeters
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009-2012  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief Justification heuristic for decision making
 **
 ** A ATGP-inspired justification-based decision heuristic. This code is based
 ** on the CVC3 implementation of the same heuristic -- note below.
 **
 ** It needs access to the simplified but non-clausal formula.
 **/

#include "justification_heuristic.h"

#include "expr/node_manager.h"
#include "expr/kind.h"
#include "theory/rewriter.h"
#include "util/ite_removal.h"

void JustificationHeuristic::setJustified(TNode n)
{
  d_justified.insert(n);
}

bool JustificationHeuristic::checkJustified(TNode n)
{
  return d_justified.find(n) != d_justified.end();
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

void JustificationHeuristic::computeITEs(TNode n, IteList &l)
{
  Trace("jh-ite") << " computeITEs( " << n << ", &l)\n";
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

const JustificationHeuristic::IteList& JustificationHeuristic::getITEs(TNode n)
{
  IteCache::iterator it = d_iteCache.find(n);
  if(it != d_iteCache.end()) {
    return it->second;
  } else {
    // Compute the list of ITEs
    // TODO: optimize by avoiding multiple lookup for d_iteCache[n]
    d_iteCache[n] = IteList();
    d_visitedComputeITE.clear();
    computeITEs(n, d_iteCache[n]);
    return d_iteCache[n];
  }
}

bool JustificationHeuristic::findSplitterRec(TNode node, 
                                             SatValue desiredVal)
{
  /**
   * Main idea
   *
   * Given a boolean formula "node", the goal is to try to make it
   * evaluate to "desiredVal" (true/false). for instance if "node" is a AND
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
    return false;
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
  Assert(desiredVal != SAT_VALUE_UNKNOWN, "expected known value");

  /* Good luck, hope you can get what you want */
  Assert(litVal == desiredVal || litVal == SAT_VALUE_UNKNOWN,
         "invariant violated");

  /* What type of node is this */
  Kind k = node.getKind();	
  theory::TheoryId tId = theory::kindToTheoryId(k);

  /* Some debugging stuff */
  Debug("decision::jh") << "kind = " << k << std::endl
                        << "theoryId = " << tId << std::endl
                        << "node = " << node << std::endl
                        << "litVal = " << litVal << std::endl;

  /**
   * If not in theory of booleans, and not a "boolean" EQUAL (IFF),
   * then check if this is something to split-on.
   */
  if(tId != theory::THEORY_BOOL) {

    // if node has embedded ites, resolve that first
    const IteList& l = getITEs(node);
    Trace("jh-ite") << " ite size = " << l.size() << std::endl;
    /*d_visited.insert(node);*/
    for(IteList::const_iterator i = l.begin(); i != l.end(); ++i) {
      if(d_visited.find(i->first) == d_visited.end()) {
        d_visited.insert(i->first);
        Debug("jh-ite") << "jh-ite: adding visited " << i->first << std::endl;
        if(findSplitterRec(i->second, SAT_VALUE_TRUE))
          return true;
        Debug("jh-ite") << "jh-ite: removing visited " << i->first << std::endl;
        d_visited.erase(i->first);
      } else {
        Debug("jh-ite") << "jh-ite: already visited " << i->first << std::endl;
      }
    }

    if(litVal != SAT_VALUE_UNKNOWN) {
      setJustified(node);
      return false;
    } else {
      Assert(d_decisionEngine->hasSatLiteral(node));
      SatVariable v = 
        d_decisionEngine->getSatLiteral(node).getSatVariable();
      d_curDecision =
        SatLiteral(v, desiredVal != SAT_VALUE_TRUE );
      Trace("decision") << "decision " << d_curDecision << std::endl;
      return true;
    }
  }

  bool ret = false;
  switch (k) {

  case kind::CONST_BOOLEAN:
    Assert(node.getConst<bool>() == false || desiredVal == SAT_VALUE_TRUE);
    Assert(node.getConst<bool>() == true  || desiredVal == SAT_VALUE_FALSE);
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

  case kind::IFF: {
    SatValue desiredVal1 = tryGetSatValue(node[0]);
    SatValue desiredVal2 = tryGetSatValue(node[1]);

    if(desiredVal1 == SAT_VALUE_UNKNOWN &&
       desiredVal2 == SAT_VALUE_UNKNOWN) {
      // CHOICE: pick one of them arbitarily
      desiredVal1 = SAT_VALUE_FALSE;
    }

    if(desiredVal2 == SAT_VALUE_UNKNOWN) {
      desiredVal2 =
        desiredVal == SAT_VALUE_TRUE ?
        desiredVal1 : invertValue(desiredVal1);
    } else if(desiredVal1 == SAT_VALUE_UNKNOWN) {
      desiredVal1 =
        desiredVal == SAT_VALUE_TRUE ?
        desiredVal2 : invertValue(desiredVal2);
    }

    ret = handleBinaryHard(node[0], desiredVal1,
                           node[1], desiredVal2);
    break;
  }
    
  case kind::XOR:{
    SatValue desiredVal1 = tryGetSatValue(node[0]);
    SatValue desiredVal2 = tryGetSatValue(node[1]);

    if(desiredVal1 == SAT_VALUE_UNKNOWN &&
       desiredVal2 == SAT_VALUE_UNKNOWN) {
      // CHOICE: pick one of them arbitarily
      desiredVal1 = SAT_VALUE_FALSE;
    }

    if(desiredVal2 == SAT_VALUE_UNKNOWN) {
      desiredVal2 =
        desiredVal == SAT_VALUE_FALSE ?
        desiredVal1 : invertValue(desiredVal1);
    } else if(desiredVal1 == SAT_VALUE_UNKNOWN) {
      desiredVal1 =
        desiredVal == SAT_VALUE_FALSE ?
        desiredVal2 : invertValue(desiredVal2);
    }

    ret = handleBinaryHard(node[0], desiredVal1,
                           node[1], desiredVal2);
    break;
  }

  case kind::ITE: {
    //[0]: if, [1]: then, [2]: else
    SatValue ifVal = tryGetSatValue(node[0]);
    if (ifVal == SAT_VALUE_UNKNOWN) {
      
      // are we better off trying false? if not, try true
      SatValue ifDesiredVal = 
        (tryGetSatValue(node[2]) == desiredVal ||
	 tryGetSatValue(node[1]) == invertValue(desiredVal))
	? SAT_VALUE_FALSE : SAT_VALUE_TRUE;

      if(findSplitterRec(node[0], ifDesiredVal)) {
	return true;
      }
      Assert(false, "No controlling input found (6)");
    } else {

      // Try to justify 'if'
      if (findSplitterRec(node[0], ifVal)) {
	return true;
      }

      // If that was successful, we need to go into only one of 'then'
      // or 'else'
      int ch = (ifVal == SAT_VALUE_TRUE) ? 1 : 2;
      int chVal = tryGetSatValue(node[ch]);
      if( (chVal == SAT_VALUE_UNKNOWN || chVal == desiredVal)
	  && findSplitterRec(node[ch], desiredVal) ) {
	return true;
      }
    }
    Assert(litPresent == false || litVal == desiredVal,
	   "Output should be justified");
    setJustified(node);
    return false;
  }

  default:
    Assert(false, "Unexpected Boolean operator");
    break;
  }//end of switch(k)

  if(ret == false) {
    Assert(litPresent == false || litVal ==  desiredVal,
           "Output should be justified");
    setJustified(node);
  }
  return ret;
}/* findRecSplit method */

bool JustificationHeuristic::handleAndOrEasy(TNode node, SatValue desiredVal) {
  Assert( (node.getKind() == kind::AND and desiredVal == SAT_VALUE_FALSE) or 
          (node.getKind() == kind::OR  and desiredVal == SAT_VALUE_TRUE) );

  int numChildren = node.getNumChildren();
  SatValue desiredValInverted = invertValue(desiredVal);
  for(int i = 0; i < numChildren; ++i)
    if ( tryGetSatValue(node[i]) != desiredValInverted )
      return findSplitterRec(node[i], desiredVal);
  Assert(false, "handleAndOrEasy: No controlling input found");
  return false;
}

bool JustificationHeuristic::handleAndOrHard(TNode node, SatValue desiredVal) {
  Assert( (node.getKind() == kind::AND and desiredVal == SAT_VALUE_TRUE) or 
          (node.getKind() == kind::OR  and desiredVal == SAT_VALUE_FALSE) );

  int numChildren = node.getNumChildren();
  for(int i = 0; i < numChildren; ++i)
    if (findSplitterRec(node[i], desiredVal))
      return true;
  return false;
}

bool JustificationHeuristic::handleBinaryEasy
(TNode node1, SatValue desiredVal1, TNode node2, SatValue desiredVal2)
{
  if ( tryGetSatValue(node1) != invertValue(desiredVal1) )
    return findSplitterRec(node1, desiredVal1);
  if ( tryGetSatValue(node2) != invertValue(desiredVal2) )
    return findSplitterRec(node2, desiredVal2);
  Assert(false, "handleBinaryEasy: No controlling input found");
  return false;
}

bool JustificationHeuristic::handleBinaryHard
(TNode node1, SatValue desiredVal1, TNode node2, SatValue desiredVal2)
{
  if( findSplitterRec(node1, desiredVal1) )
    return true;
  return findSplitterRec(node2, desiredVal2);
}
