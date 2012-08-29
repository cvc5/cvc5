/*********************                                                        */
/*! \file justification_heuristic.cpp
 ** \verbatim
 ** Original author: kshitij
 ** Major contributors: none
 ** Minor contributors (to current version): dejan
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009-2012  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief Justification heuristic for decision making
 **
 ** A ATGP-inspired justification-based decision heuristic. See
 ** [insert reference] for more details. This code is, or not, based
 ** on the CVC3 implementation of the same heuristic -- note below.
 **
 ** It needs access to the simplified but non-clausal formula.
 **/
/*****************************************************************************/
/*!
 * file search_sat.cpp
 * brief Implementation of Search engine with generic external sat solver
 *
 * Author: Clark Barrett
 *
 * Created: Wed Dec  7 21:00:24 2005
 *
 * <hr>
 *
 * License to use, copy, modify, sell and/or distribute this software
 * and its documentation for any purpose is hereby granted without
 * royalty, subject to the terms and conditions defined in the \ref
 * LICENSE file provided with this distribution.
 * 
 * <hr>
 */
/*****************************************************************************/

#include "justification_heuristic.h"

#include "expr/node_manager.h"
#include "expr/kind.h"
#include "theory/rewriter.h"
#include "util/ite_removal.h"

/***
Here's the main idea

   Given a boolean formula "node", the goal is to try to make it
evaluate to "desiredVal" (true/false). for instance if "node" is a AND
formula we want to make it evaluate to true, we'd like one of the
children to be true. this is done recursively.

***/

/*

CVC3 code <---->  this code
 
 value            desiredVal
 getValue(lit)    litVal

***/


// Local helper functions for just this file



// JustificationHeuristic stuff

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
  for(unsigned i=0; i<n.getNumChildren(); ++i) {
    SkolemMap::iterator it2 = d_iteAssertions.find(n[i]);
    if(it2 != d_iteAssertions.end()) {
      l.push_back(make_pair(n[i], it2->second));
      Assert(n[i].getNumChildren() == 0);
    }
    computeITEs(n[i], l);
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
    computeITEs(n, d_iteCache[n]);
    return d_iteCache[n];
  }
}

bool JustificationHeuristic::findSplitterRec(TNode node, 
                                             SatValue desiredVal,
                                             SatLiteral* litDecision)
{
  Trace("jh-findSplitterRec") 
    << "findSplitterRec(" << node << ", " 
    << desiredVal << ", .. )" << std::endl; 

  /* Handle NOT as a special case */
  while (node.getKind() == kind::NOT) {
    desiredVal = invertValue(desiredVal);
    node = node[0];
  }

  if(Debug.isOn("decision")) {
    if(checkJustified(node))
      Debug("decision") << "  justified, returning" << std::endl; 
  }

  /* Base case */
  if (checkJustified(node)) {
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
  //Assert(litPresent); -- fails
#endif

  // Get value of sat literal for the node, if there is one
  SatValue litVal = tryGetSatValue(node);

  /* You'd better know what you want */
  Assert(desiredVal != SAT_VALUE_UNKNOWN, "expected known value");

  /* Good luck, hope you can get what you want */
  // if(not (litVal == desiredVal || litVal == SAT_VALUE_UNKNOWN)) {
  //   Warning() << "WARNING: IMPORTANT: Please look into this. Sat solver is asking for a decision" << std::endl
  //             << "when the assertion we are trying to justify is already unsat. OR there is a bug" << std::endl;
  //   GiveUpException();
  // }
  Assert(litVal == desiredVal || litVal == SAT_VALUE_UNKNOWN,
         "invariant violated");

  /* What type of node is this */
  Kind k = node.getKind();	
  theory::TheoryId tId = theory::kindToTheoryId(k);

  /* Some debugging stuff */
  Debug("jh-findSplitterRec") << "kind = " << k << std::endl;
  Debug("jh-findSplitterRec") << "theoryId = " << tId << std::endl;
  Debug("jh-findSplitterRec") << "node = " << node << std::endl;
  Debug("jh-findSplitterRec") << "litVal = " << litVal << std::endl;

  /**
   * If not in theory of booleans, and not a "boolean" EQUAL (IFF),
   * then check if this is something to split-on.
   */
  if(tId != theory::THEORY_BOOL
     //      && !(k == kind::EQUAL && node[0].getType().isBoolean()) 
     ) {

    // if node has embedded ites -- which currently happens iff it got
    // replaced during ite removal -- then try to resolve that first
    const IteList& l = getITEs(node);
    Trace("jh-ite") << " ite size = " << l.size() << std::endl;
    /*d_visited.insert(node);*/
    for(IteList::const_iterator i = l.begin(); i != l.end(); ++i) {
      if(d_visited.find(i->first) == d_visited.end()) {
        d_visited.insert(i->first);
        Debug("jh-ite") << "jh-ite: adding visited " << i->first << std::endl;
        if(findSplitterRec(i->second, SAT_VALUE_TRUE, litDecision))
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
      /* if(not d_decisionEngine->hasSatLiteral(node))
         throw GiveUpException(); */
      Assert(d_decisionEngine->hasSatLiteral(node));
      SatVariable v = d_decisionEngine->getSatLiteral(node).getSatVariable();
      *litDecision = SatLiteral(v, desiredVal != SAT_VALUE_TRUE );
      Trace("decision") << "decision " << *litDecision << std::endl;
      Trace("decision") << "Found something to split. Glad to be able to serve you." << std::endl;
      return true;
    }
  }

  SatValue valHard = SAT_VALUE_FALSE;
  switch (k) {

  case kind::CONST_BOOLEAN:
    Assert(node.getConst<bool>() == false || desiredVal == SAT_VALUE_TRUE);
    Assert(node.getConst<bool>() == true || desiredVal == SAT_VALUE_FALSE);
    setJustified(node);
    return false;

  case kind::AND:
    valHard = SAT_VALUE_TRUE;

  case kind::OR:
    if (desiredVal == valHard) {
      int n = node.getNumChildren();
      for(int i = 0; i < n; ++i) {
        if (findSplitterRec(node[i], valHard, litDecision)) {
          return true;
        }
      }
      Assert(litPresent == false || litVal == valHard,
             "Output should be justified");
      setJustified(node);
      return false;
    }
    else {
      SatValue valEasy = invertValue(valHard);
      int n = node.getNumChildren();
      for(int i = 0; i < n; ++i) {
        Debug("jh-findSplitterRec") << " node[i] = " << node[i] << " " 
                                 << tryGetSatValue(node[i]) << std::endl;
        if ( tryGetSatValue(node[i]) != valHard) {
          Debug("jh-findSplitterRec") << "hi"<< std::endl;
          if (findSplitterRec(node[i], valEasy, litDecision)) {
            return true;
          }
          Assert(litPresent == false || litVal == valEasy, "Output should be justified");
          setJustified(node);
          return false;
        }
      }
      if(Debug.isOn("jh-findSplitterRec")) {
        Debug("jh-findSplitterRec") << " * ** " << std::endl;
        Debug("jh-findSplitterRec") << node.getKind() << " "
                                    << node << std::endl;
        for(unsigned i = 0; i < node.getNumChildren(); ++i) 
        Debug("jh-findSplitterRec") << "child: " << tryGetSatValue(node[i]) 
                                    << std::endl;
        Debug("jh-findSplitterRec") << "node: " << tryGetSatValue(node)
                                    << std::endl;
      }
      Assert(false, "No controlling input found (2)");
    }
    break;

  case kind::IMPLIES:
    //throw GiveUpException();
    Assert(node.getNumChildren() == 2, "Expected 2 fanins");
    if (desiredVal == SAT_VALUE_FALSE) {
      if (findSplitterRec(node[0], SAT_VALUE_TRUE, litDecision)) {
        return true;
      }
      if (findSplitterRec(node[1], SAT_VALUE_FALSE, litDecision)) {
        return true;
      }
      Assert(litPresent == false || litVal == SAT_VALUE_FALSE, 
             "Output should be justified");
      setJustified(node);
      return false;
    }
    else {
      if (tryGetSatValue(node[0]) != SAT_VALUE_TRUE) {
        if (findSplitterRec(node[0], SAT_VALUE_FALSE, litDecision)) {
          return true;
        }
        Assert(litPresent == false || litVal == SAT_VALUE_TRUE, 
               "Output should be justified");
        setJustified(node);
        return false;
      }
      if (tryGetSatValue(node[1]) != SAT_VALUE_FALSE) {
        if (findSplitterRec(node[1], SAT_VALUE_TRUE, litDecision)) {
          return true;
        }
        Assert(litPresent == false || litVal == SAT_VALUE_TRUE, 
               "Output should be justified");
        setJustified(node);
        return false;
      }
      Assert(false, "No controlling input found (3)");
    }
    break;

  case kind::IFF: 
    //throw GiveUpException();
    {
    SatValue val = tryGetSatValue(node[0]);
    if (val != SAT_VALUE_UNKNOWN) {
      if (findSplitterRec(node[0], val, litDecision)) {
        return true;
      }
      if (desiredVal == SAT_VALUE_FALSE) val = invertValue(val);

      if (findSplitterRec(node[1], val, litDecision)) {
        return true;
      }
      Assert(litPresent == false || litVal == desiredVal, 
             "Output should be justified");
      setJustified(node);
      return false;
    }
    else {
      val = tryGetSatValue(node[1]);
      if (val == SAT_VALUE_UNKNOWN) val = SAT_VALUE_FALSE;
      if (desiredVal == SAT_VALUE_FALSE) val = invertValue(val);
      if (findSplitterRec(node[0], val, litDecision)) {
        return true;
      }
      Assert(false, "Unable to find controlling input (4)");
    }
    break;
  }
    
  case kind::XOR:
    //throw GiveUpException();
    {
    SatValue val = tryGetSatValue(node[0]);
    if (val != SAT_VALUE_UNKNOWN) {
      if (findSplitterRec(node[0], val, litDecision)) {
        return true;
      }
      if (desiredVal == SAT_VALUE_TRUE) val = invertValue(val);

      if (findSplitterRec(node[1], val, litDecision)) {
        return true;
      }
      Assert(litPresent == false || litVal == desiredVal, 
             "Output should be justified");
      setJustified(node);
      return false;
    }
    else {
      SatValue val = tryGetSatValue(node[1]);
      if (val == SAT_VALUE_UNKNOWN) val = SAT_VALUE_FALSE;
      if (desiredVal == SAT_VALUE_TRUE) val = invertValue(val);
      if (findSplitterRec(node[0], val, litDecision)) {
        return true;
      }
      Assert(false, "Unable to find controlling input (5)");
    }
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

      if(findSplitterRec(node[0], ifDesiredVal, litDecision)) {
	return true;
      }
      Assert(false, "No controlling input found (6)");
    } else {

      // Try to justify 'if'
      if (findSplitterRec(node[0], ifVal, litDecision)) {
	return true;
      }

      // If that was successful, we need to go into only one of 'then'
      // or 'else'
      int ch = (ifVal == SAT_VALUE_TRUE) ? 1 : 2;
      int chVal = tryGetSatValue(node[ch]);
      if( (chVal == SAT_VALUE_UNKNOWN || chVal == desiredVal)
	  && findSplitterRec(node[ch], desiredVal, litDecision) ) {
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

  Unreachable();
}/* findRecSplit method */
