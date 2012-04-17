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


/***

Summary of the algorithm:



***/

/*

CVC3 code <---->  this code
 
 value            desiredVal
 getValue(lit)    litVal

***/

void JustificationHeuristic::setJustified(SatVariable v)
{
  d_justified.insert(v);
}

bool JustificationHeuristic::checkJustified(SatVariable v)
{
  return d_justified.find(v) != d_justified.end();
}

SatValue invertValue(SatValue v)
{
  if(v == SAT_VALUE_UNKNOWN) return SAT_VALUE_UNKNOWN;
  else if(v == SAT_VALUE_TRUE) return SAT_VALUE_FALSE;
  else return SAT_VALUE_TRUE;
}

bool JustificationHeuristic::findSplitterRec(SatLiteral lit, SatValue desiredVal, SatLiteral* litDecision)
//bool SearchSat::findSplitterRec(Lit lit, Var::Val value, Lit* litDecision)
{
  // if(not ) {
  //   //    Warning() << "JustificationHeuristic encountered a variable not in SatSolver." << std::endl;
  //   return false;
  //   //    Assert(not lit.isNull());
  // }

  /** 
   * TODO -- Base case. Way CVC3 seems to handle is that it has
   * literals correpsonding to true and false. We'll have to take care
   * somewhere else.
   */

  // Var v = lit.getVar();
  SatVariable v = lit.getSatVariable();
  SatValue litVal =  d_decisionEngine->getSatValue(lit);

  // if (lit.isFalse() || lit.isTrue()) return false;
  if (v == 0) return false;


  /* You'd better know what you want */
  // DebugAssert(value != Var::UNKNOWN, "expected known value");
  Assert(desiredVal != SAT_VALUE_UNKNOWN, "expected known value");

  /* Good luck, hope you can get what you want */
  // DebugAssert(getValue(lit) == value || getValue(lit) == Var::UNKNOWN,
  //             "invariant violated");
  Assert(litVal == desiredVal || litVal == SAT_VALUE_UNKNOWN, 
         "invariant voilated");


  if (checkJustified(v)) return false;

  if (lit.isNegated()) {
    desiredVal = invertValue(desiredVal);
  }

  Node node = d_decisionEngine->getNode(lit);
  Trace("decision") << "lit = " << lit << std::endl;
  Trace("decision") << node.getKind() << std::endl;
  Trace("decision") << node << std::endl;

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
  if(node.getNumChildren() == 0) {
    if(litVal != SAT_VALUE_UNKNOWN) {
      setJustified(v);
      return false;
    } else {
      *litDecision = SatLiteral(v, desiredVal == SAT_VALUE_TRUE );
      return true;
    }
  }


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

  int kind = d_cnfManager->concreteVar(v).getKind();
  Var::Val valHard = Var::FALSE_VAL;
  switch (kind) {
    case AND:
      valHard = Var::TRUE_VAL;
    case OR:
      if (value == valHard) {
        n = d_cnfManager->numFanins(v);
        for (i=0; i < n; ++i) {
          litTmp = d_cnfManager->getFanin(v, i);
          if (findSplitterRec(litTmp, valHard, litDecision)) {
            return true;
          }
        }
        DebugAssert(getValue(v) == valHard, "Output should be justified");
        setJustified(v);
        return false;
      }
      else {
        Var::Val valEasy = Var::invertValue(valHard);
        n = d_cnfManager->numFanins(v);
        for (i=0; i < n; ++i) {
          litTmp = d_cnfManager->getFanin(v, i);
          if (getValue(litTmp) != valHard) {
            if (findSplitterRec(litTmp, valEasy, litDecision)) {
              return true;
            }
            DebugAssert(getValue(v) == valEasy, "Output should be justified");
            setJustified(v);
            return false;
          }
        }
        DebugAssert(false, "No controlling input found (2)");
      }
      break;
    case IMPLIES:
      DebugAssert(d_cnfManager->numFanins(v) == 2, "Expected 2 fanins");
      if (value == Var::FALSE_VAL) {
        litTmp = d_cnfManager->getFanin(v, 0);
        if (findSplitterRec(litTmp, Var::TRUE_VAL, litDecision)) {
          return true;
        }
        litTmp = d_cnfManager->getFanin(v, 1);
        if (findSplitterRec(litTmp, Var::FALSE_VAL, litDecision)) {
          return true;
        }
        DebugAssert(getValue(v) == Var::FALSE_VAL, "Output should be justified");
        setJustified(v);
        return false;
      }
      else {
        litTmp = d_cnfManager->getFanin(v, 0);
        if (getValue(litTmp) != Var::TRUE_VAL) {
          if (findSplitterRec(litTmp, Var::FALSE_VAL, litDecision)) {
            return true;
          }
          DebugAssert(getValue(v) == Var::TRUE_VAL, "Output should be justified");
          setJustified(v);
          return false;
        }
        litTmp = d_cnfManager->getFanin(v, 1);
        if (getValue(litTmp) != Var::FALSE_VAL) {
          if (findSplitterRec(litTmp, Var::TRUE_VAL, litDecision)) {
            return true;
          }
          DebugAssert(getValue(v) == Var::TRUE_VAL, "Output should be justified");
          setJustified(v);
          return false;
        }
        DebugAssert(false, "No controlling input found (3)");
      }
      break;
    case IFF: {
      litTmp = d_cnfManager->getFanin(v, 0);
      Var::Val val = getValue(litTmp);
      if (val != Var::UNKNOWN) {
        if (findSplitterRec(litTmp, val, litDecision)) {
          return true;
        }
        if (value == Var::FALSE_VAL) val = Var::invertValue(val);
        litTmp = d_cnfManager->getFanin(v, 1);

        if (findSplitterRec(litTmp, val, litDecision)) {
          return true;
        }
        DebugAssert(getValue(v) == value, "Output should be justified");
        setJustified(v);
        return false;
      }
      else {
        val = getValue(d_cnfManager->getFanin(v, 1));
        if (val == Var::UNKNOWN) val = Var::FALSE_VAL;
        if (value == Var::FALSE_VAL) val = Var::invertValue(val);
        if (findSplitterRec(litTmp, val, litDecision)) {
          return true;
        }
        DebugAssert(false, "Unable to find controlling input (4)");
      }
      break;
    }
    case XOR: {
      litTmp = d_cnfManager->getFanin(v, 0);
      Var::Val val = getValue(litTmp);
      if (val != Var::UNKNOWN) {
        if (findSplitterRec(litTmp, val, litDecision)) {
          return true;
        }
        if (value == Var::TRUE_VAL) val = Var::invertValue(val);
        litTmp = d_cnfManager->getFanin(v, 1);
        if (findSplitterRec(litTmp, val, litDecision)) {
          return true;
        }
        DebugAssert(getValue(v) == value, "Output should be justified");
        setJustified(v);
        return false;
      }
      else {
        val = getValue(d_cnfManager->getFanin(v, 1));
        if (val == Var::UNKNOWN) val = Var::FALSE_VAL;
        if (value == Var::TRUE_VAL) val = Var::invertValue(val);
        if (findSplitterRec(litTmp, val, litDecision)) {
          return true;
        }
        DebugAssert(false, "Unable to find controlling input (5)");
      }
      break;
    }
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
    default:
      DebugAssert(false, "Unexpected Boolean operator");
      break;
  }
  FatalAssert(false, "Should be unreachable");
  ------------------------------------------------  */
  return false;

  Unreachable();

}/* findRecSplit method */
