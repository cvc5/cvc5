/*********************                                                        */
/*! \file justification_heuristic.h
 ** \verbatim
 ** Original author: kshitij
 ** Major contributors: none
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2012  The Analysis of Computer Systems Group (ACSys)
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
 *\file search_sat.cpp
 *\brief Implementation of Search engine with generic external sat solver
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

#include "expr/kind.h"

/***

Summary of the algorithm:



***/

/*

CVC3 code <---->  this code
 
 value            desiredVal
 getValue(lit)    litVal

***/

void JustificationHeuristic::setJustified(TNode n)
{
  d_justified.insert(n);
}

bool JustificationHeuristic::checkJustified(TNode n)
{
  return d_justified.find(n) != d_justified.end();
}

SatValue invertValue(SatValue v)
{
  if(v == SAT_VALUE_UNKNOWN) return SAT_VALUE_UNKNOWN;
  else if(v == SAT_VALUE_TRUE) return SAT_VALUE_FALSE;
  else return SAT_VALUE_TRUE;
}

bool JustificationHeuristic::findSplitterRec(Node node, SatValue desiredVal, SatLiteral* litDecision)
//bool SearchSat::findSplitterRec(Lit lit, Var::Val value, Lit* litDecision)
{
  Trace("decision") 
    << "findSplitterRec(" << node << ", " << desiredVal << ", .. )" << std::endl; 

  /* Handle NOT as a special case */
  if (node.getKind() == kind::NOT) {
    desiredVal = invertValue(desiredVal);
    node = node[0];
  }

  if (checkJustified(node)) return false;

  SatValue litVal = tryGetSatValue(node);
  bool litPresent = false;
  if(d_decisionEngine->hasSatLiteral(node) ) {
    SatLiteral lit = d_decisionEngine->getSatLiteral(node);
    litPresent = true;

    SatVariable v = lit.getSatVariable();
    // if (lit.isFalse() || lit.isTrue()) return false;
    if (v == 0) {
      setJustified(node);
      return false;
    }
  } else {
    Trace("decision") << "no sat literal for this node" << std::endl;
  }


  /* You'd better know what you want */
  Assert(desiredVal != SAT_VALUE_UNKNOWN, "expected known value");

  /* Good luck, hope you can get what you want */
  Assert(litVal == desiredVal || litVal == SAT_VALUE_UNKNOWN, 
         "invariant voilated");

  /* What type of node is this */
  Kind k = node.getKind();
  theory::TheoryId tId = theory::kindToTheoryId(k);

  /* Some debugging stuff */
  Trace("findSpitterRec") << "kind = " << k << std::endl;
  Trace("findSplitterRec") << "theoryId = " << tId << std::endl;
  Trace("findSplitterRec") << "node = " << node << std::endl;
  Trace("findSplitterRec") << "litVal = " << litVal << std::endl;

  /*
  if (d_cnfManager->numFanins(v) == 0) {
    if (getValue(v) != Var::UNKNOWN) {
      setJustified(v);
      return false;
    }
    else {
      *litDecision = Lit(v, value == Var::TRUE_VAL);
      return true;
    }
  }
  */


  /**
   * If not in theory of booleans, and not a "boolean" EQUAL (IFF),
   * then check if this is something to split-on? 
   */
  if(tId != theory::THEORY_BOOL
     //      && !(k == kind::EQUAL && node[0].getType().isBoolean()) 
     ) {
    if(litVal != SAT_VALUE_UNKNOWN) {
      setJustified(node);
      return false;
    } else {
      if(not d_decisionEngine->hasSatLiteral(node))
        throw GiveUpException();
      Assert(d_decisionEngine->hasSatLiteral(node));
      SatVariable v = d_decisionEngine->getSatLiteral(node).getSatVariable();
      *litDecision = SatLiteral(v, desiredVal != SAT_VALUE_TRUE );
      Trace("decision") << "decision " << *litDecision << std::endl;
      Trace("decision") << "Found something to split. Glad to be able to serve you." << std::endl;
      return true;
    }
  }


  /*** TODO: Term ITEs ***/
  /*
  else if (d_cnfManager->concreteVar(v).isAbsAtomicFormula()) {
    // This node represents a predicate with embedded ITE's
    // We handle this case specially in order to catch the
    // corner case when a variable is in its own fanin.
    n = d_cnfManager->numFanins(v);
    for (i=0; i < n; ++i) {
      litTmp = d_cnfManager->getFanin(v, i);
      varTmp = litTmp.getVar();
      DebugAssert(!litTmp.isInverted(),"Expected positive fanin");
      if (checkJustified(varTmp)) continue;
      DebugAssert(d_cnfManager->concreteVar(varTmp).getKind() == ITE,
                  "Expected ITE");
      DebugAssert(getValue(varTmp) == Var::TRUE_VAL,"Expected TRUE");
      Lit cIf = d_cnfManager->getFanin(varTmp,0);
      Lit cThen = d_cnfManager->getFanin(varTmp,1);
      Lit cElse = d_cnfManager->getFanin(varTmp,2);
      if (getValue(cIf) == Var::UNKNOWN) {
        if (getValue(cElse) == Var::TRUE_VAL ||
            getValue(cThen) == Var::FALSE_VAL) {
          ret = findSplitterRec(cIf, Var::FALSE_VAL, litDecision);
        }
        else {
          ret = findSplitterRec(cIf, Var::TRUE_VAL, litDecision);
        }
        if (!ret) {
          cout << d_cnfManager->concreteVar(cIf.getVar()) << endl;
          DebugAssert(false,"No controlling input found (1)");
        }	  
        return true;
      }
      else if (getValue(cIf) == Var::TRUE_VAL) {
        if (findSplitterRec(cIf, Var::TRUE_VAL, litDecision)) {
            return true;
        }
        if (cThen.getVar() != v &&
            (getValue(cThen) == Var::UNKNOWN ||
             getValue(cThen) == Var::TRUE_VAL) &&
            findSplitterRec(cThen, Var::TRUE_VAL, litDecision)) {
          return true;
        }
      }
      else {
        if (findSplitterRec(cIf, Var::FALSE_VAL, litDecision)) {
          return true;
        }
        if (cElse.getVar() != v &&
            (getValue(cElse) == Var::UNKNOWN ||
             getValue(cElse) == Var::TRUE_VAL) &&
            findSplitterRec(cElse, Var::TRUE_VAL, litDecision)) {
          return true;
        }
      }
      setJustified(varTmp);
    }
    if (getValue(v) != Var::UNKNOWN) {
      setJustified(v);
      return false;
    }
    else {
      *litDecision = Lit(v, value == Var::TRUE_VAL);
      return true;
    }
  }
  */

  SatValue valHard = SAT_VALUE_FALSE;
  switch (k) {
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
      Assert(litPresent == false || litVal == valHard, "Output should be justified");
      setJustified(node);
      return false;
    }
    else {
      SatValue valEasy = invertValue(valHard);
      int n = node.getNumChildren();
      for(int i = 0; i < n; ++i) {
        Trace("findSplitterRec") << " node[i] = " << node[i] << " " << tryGetSatValue(node[i]) << std::endl;
        if ( tryGetSatValue(node[i]) != valHard) {
          Trace("findSplitterRec") << "hi"<< std::endl;
          if (findSplitterRec(node[i], valEasy, litDecision)) {
            return true;
          }
          Assert(litPresent == false || litVal == valEasy, "Output should be justified");
          setJustified(node);
          return false;
        }
      }
      Trace("findSplitterRec") << " * ** " << std::endl;
      Trace("findSplitterRec") << node.getKind() << " " << node << std::endl;
      for(unsigned i = 0; i < node.getNumChildren(); ++i) 
        Trace("findSplitterRec") << "child: " << tryGetSatValue(node[i]) << std::endl;
      Trace("findSplitterRec") << "node: " << tryGetSatValue(node) << std::endl;
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
      Assert(litPresent == false || litVal == SAT_VALUE_FALSE, "Output should be justified");
      setJustified(node);
      return false;
    }
    else {
      if (tryGetSatValue(node[0]) != SAT_VALUE_TRUE) {
        if (findSplitterRec(node[0], SAT_VALUE_FALSE, litDecision)) {
          return true;
        }
        Assert(litPresent == false || litVal == SAT_VALUE_TRUE, "Output should be justified");
        setJustified(node);
        return false;
      }
      if (tryGetSatValue(node[1]) != SAT_VALUE_FALSE) {
        if (findSplitterRec(node[1], SAT_VALUE_TRUE, litDecision)) {
          return true;
        }
        Assert(litPresent == false || litVal == SAT_VALUE_TRUE, "Output should be justified");
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
      Assert(litPresent == false || litVal == desiredVal, "Output should be justified");
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
      Assert(litPresent == false || litVal == desiredVal, "Output should be justified");
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

  case kind::ITE:
    throw GiveUpException();
    /*
    case ITE: {
      Lit cIf = d_cnfManager->getFanin(v, 0);
      Lit cThen = d_cnfManager->getFanin(v, 1);
      Lit cElse = d_cnfManager->getFanin(v, 2);
      if (getValue(cIf) == Var::UNKNOWN) {
        if (getValue(cElse) == value ||
            getValue(cThen) == Var::invertValue(value)) {
          ret = findSplitterRec(cIf, Var::FALSE_VAL, litDecision);
        }
        else {
          ret = findSplitterRec(cIf, Var::TRUE_VAL, litDecision);
        }
        if (!ret) {
          cout << d_cnfManager->concreteVar(cIf.getVar()) << endl;
          DebugAssert(false,"No controlling input found (6)");
        }	  
        return true;
      }
      else if (getValue(cIf) == Var::TRUE_VAL) {
        if (findSplitterRec(cIf, Var::TRUE_VAL, litDecision)) {
            return true;
        }
        if (cThen.isVar() && cThen.getVar() != v &&
            (getValue(cThen) == Var::UNKNOWN ||
             getValue(cThen) == value) &&
            findSplitterRec(cThen, value, litDecision)) {
          return true;
        }
      }
      else {
        if (findSplitterRec(cIf, Var::FALSE_VAL, litDecision)) {
          return true;
        }
        if (cElse.isVar() && cElse.getVar() != v &&
            (getValue(cElse) == Var::UNKNOWN ||
             getValue(cElse) == value) &&
            findSplitterRec(cElse, value, litDecision)) {
          return true;
        }
      }
      DebugAssert(getValue(v) == value, "Output should be justified");
      setJustified(v);
      return false;
    }
      */
  default:
    Assert(false, "Unexpected Boolean operator");
    break;
  }

  /* Swap order of these two once we handle all cases */
  return false;
  Unreachable();


}/* findRecSplit method */
