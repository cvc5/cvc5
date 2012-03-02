/*********************                                                        */
/*! \file arith_prop_manager.cpp
 ** \verbatim
 ** Original author: taking
 ** Major contributors: none
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010, 2011  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief [[ Add one-line brief description here ]]
 **
 ** [[ Add lengthier description here ]]
 ** \todo document this file
 **/


#include "theory/arith/arith_prop_manager.h"

#include "theory/arith/arith_utilities.h"
#include "context/context.h"
#include "context/cdlist.h"
#include "context/cdhashmap.h"
#include "context/cdo.h"

using namespace CVC4;
using namespace CVC4::theory;
using namespace CVC4::theory::arith;
using namespace CVC4::kind;
using namespace std;


bool ArithPropManager::isAsserted(TNode n) const{
  Node satValue = d_valuation.getSatValue(n);
  if(satValue.isNull()){
    return false;
  }else{
    //Assert(satValue.getConst<bool>());
    return true;
  }
}


Node ArithPropManager::strictlyWeakerAssertedUpperBound(ArithVar v, const DeltaRational& b) const{
  Node bound = boundAsNode(true, v, b);

  Assert(b.getInfinitesimalPart() <= 0);
  bool largeEpsilon = (b.getInfinitesimalPart() < -1);

  Node weaker = bound;
  do {
    if(largeEpsilon){
      weaker = d_atomDatabase.getBestImpliedUpperBound(weaker);
      largeEpsilon = false;
    }else{
      weaker = d_atomDatabase.getWeakerImpliedUpperBound(weaker);
    }
  }while(!weaker.isNull() && !isAsserted(weaker));
  return weaker;
}

Node ArithPropManager::strictlyWeakerAssertedLowerBound(ArithVar v, const DeltaRational& b) const{
  Debug("ArithPropManager") << "strictlyWeakerAssertedLowerBound" << endl;
  Node bound = boundAsNode(false, v, b);

  Assert(b.getInfinitesimalPart() >= 0);
  bool largeEpsilon = (b.getInfinitesimalPart() > 1);

  Node weaker = bound;
  Debug("ArithPropManager") << bound << b << endl;
  do {
    if(largeEpsilon){
      weaker = d_atomDatabase.getBestImpliedLowerBound(weaker);
      largeEpsilon = false;
    }else{
      weaker = d_atomDatabase.getWeakerImpliedLowerBound(weaker);
    }
  }while(!weaker.isNull() && !isAsserted(weaker));
  Debug("ArithPropManager") << "res: " << weaker << endl;
  return weaker;
}

Node ArithPropManager::getBestImpliedLowerBound(ArithVar v, const DeltaRational& b) const{
  Node bound = boundAsNode(false, v, b);
  return d_atomDatabase.getBestImpliedLowerBound(bound);
}
Node ArithPropManager::getBestImpliedUpperBound(ArithVar v, const DeltaRational& b) const{
  Node bound = boundAsNode(true, v, b);
  return d_atomDatabase.getBestImpliedUpperBound(bound);
}

Node ArithPropManager::boundAsNode(bool upperbound, ArithVar var, const DeltaRational& b) const {
  Assert((!upperbound) || (b.getInfinitesimalPart() <= 0) );
  Assert(upperbound || (b.getInfinitesimalPart() >= 0) );

  Node varAsNode = d_arithvarNodeMap.asNode(var);
  Kind kind;
  bool negate;
  if(upperbound){
    negate = b.getInfinitesimalPart() < 0;
    kind = negate ? GEQ : LEQ;
  } else{
    negate = b.getInfinitesimalPart() > 0;
    kind = negate ? LEQ : GEQ;
  }

  Node righthand = mkRationalNode(b.getNoninfinitesimalPart());
  Node bAsNode = NodeBuilder<2>(kind) << varAsNode << righthand;

  if(negate){
    bAsNode = NodeBuilder<1>(NOT) << bAsNode;
  }

  return bAsNode;
}

bool ArithPropManager::propagateArithVar(bool upperbound, ArithVar var, const DeltaRational& b, TNode reason){
  bool success = false;

  ++d_statistics.d_propagateArithVarCalls;

  Node bAsNode = boundAsNode(upperbound, var ,b);

  Node bestImplied = upperbound ?
    d_atomDatabase.getBestImpliedUpperBound(bAsNode):
    d_atomDatabase.getBestImpliedLowerBound(bAsNode);

  Debug("ArithPropManager") << upperbound <<","<< var <<","<< b <<","<< reason << endl
                            << bestImplied << endl;

  if(!bestImplied.isNull()){
    bool asserted = isAsserted(bestImplied);

    if( !asserted && !isPropagated(bestImplied)){
      propagate(bestImplied, reason, false);
      ++d_statistics.d_addedPropagation;
      success = true;
    }else if(!asserted){
      ++d_statistics.d_alreadyPropagatedNode;
    }else if(!isPropagated(bestImplied)){
      ++d_statistics.d_alreadySetSatLiteral;
    }
  }
  return success;
}

ArithPropManager::Statistics::Statistics():
  d_propagateArithVarCalls("arith::prop-manager::propagateArithVarCalls",0),
  d_addedPropagation("arith::prop-manager::addedPropagation",0),
  d_alreadySetSatLiteral("arith::prop-manager::alreadySetSatLiteral",0),
  d_alreadyPropagatedNode("arith::prop-manager::alreadyPropagatedNode",0)
{
  StatisticsRegistry::registerStat(&d_propagateArithVarCalls);
  StatisticsRegistry::registerStat(&d_alreadySetSatLiteral);
  StatisticsRegistry::registerStat(&d_alreadyPropagatedNode);
  StatisticsRegistry::registerStat(&d_addedPropagation);
}

ArithPropManager::Statistics::~Statistics()
{
  StatisticsRegistry::unregisterStat(&d_propagateArithVarCalls);
  StatisticsRegistry::unregisterStat(&d_alreadySetSatLiteral);
  StatisticsRegistry::unregisterStat(&d_alreadyPropagatedNode);
  StatisticsRegistry::unregisterStat(&d_addedPropagation);
}
