/*********************                                                        */
/*! \file arith_static_learner.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Tim King, Dejan Jovanovic, Morgan Deters
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief [[ Add one-line brief description here ]]
 **
 ** [[ Add lengthier description here ]]
 ** \todo document this file
 **/

#include <vector>

#include "base/output.h"
#include "expr/expr.h"
#include "expr/node_algorithm.h"
#include "options/arith_options.h"
#include "smt/smt_statistics_registry.h"
#include "theory/arith/arith_static_learner.h"
#include "theory/arith/arith_utilities.h"
#include "theory/arith/normal_form.h"
#include "theory/rewriter.h"

using namespace std;
using namespace CVC4::kind;

namespace CVC4 {
namespace theory {
namespace arith {


ArithStaticLearner::ArithStaticLearner(context::Context* userContext) :
  d_minMap(userContext),
  d_maxMap(userContext),
  d_statistics()
{
}

ArithStaticLearner::~ArithStaticLearner(){
}

ArithStaticLearner::Statistics::Statistics():
  d_iteMinMaxApplications("theory::arith::iteMinMaxApplications", 0),
  d_iteConstantApplications("theory::arith::iteConstantApplications", 0)
{
  smtStatisticsRegistry()->registerStat(&d_iteMinMaxApplications);
  smtStatisticsRegistry()->registerStat(&d_iteConstantApplications);
}

ArithStaticLearner::Statistics::~Statistics(){
  smtStatisticsRegistry()->unregisterStat(&d_iteMinMaxApplications);
  smtStatisticsRegistry()->unregisterStat(&d_iteConstantApplications);
}

void ArithStaticLearner::staticLearning(TNode n, NodeBuilder<>& learned){

  vector<TNode> workList;
  workList.push_back(n);
  TNodeSet processed;

  //Contains an underapproximation of nodes that must hold.
  TNodeSet defTrue;

  defTrue.insert(n);

  while(!workList.empty()) {
    n = workList.back();

    bool unprocessedChildren = false;
    for(TNode::iterator i = n.begin(), iend = n.end(); i != iend; ++i) {
      if(processed.find(*i) == processed.end()) {
        // unprocessed child
        workList.push_back(*i);
        unprocessedChildren = true;
      }
    }
    if(n.getKind() == AND && defTrue.find(n) != defTrue.end() ){
      for(TNode::iterator i = n.begin(), iend = n.end(); i != iend; ++i) {
        defTrue.insert(*i);
      }
    }

    if(unprocessedChildren) {
      continue;
    }

    workList.pop_back();
    // has node n been processed in the meantime ?
    if(processed.find(n) != processed.end()) {
      continue;
    }
    processed.insert(n);

    process(n,learned, defTrue);

  }
}


void ArithStaticLearner::process(TNode n, NodeBuilder<>& learned, const TNodeSet& defTrue){
  Debug("arith::static") << "===================== looking at " << n << endl;

  switch(n.getKind()){
  case ITE:
    if (expr::hasBoundVar(n))
    {
      // Unsafe with non-ground ITEs; do nothing
      Debug("arith::static")
          << "(potentially) non-ground ITE, ignoring..." << endl;
      break;
    }

    if(n[0].getKind() != EQUAL &&
       isRelationOperator(n[0].getKind())  ){
      iteMinMax(n, learned);
    }

    if((d_minMap.find(n[1]) != d_minMap.end() && d_minMap.find(n[2]) != d_minMap.end()) ||
       (d_maxMap.find(n[1]) != d_maxMap.end() && d_maxMap.find(n[2]) != d_maxMap.end())) {
      iteConstant(n, learned);
    }
    break;

  case CONST_RATIONAL:
    // Mark constants as minmax
    d_minMap.insert(n, n.getConst<Rational>());
    d_maxMap.insert(n, n.getConst<Rational>());
    break;
  default: // Do nothing
    break;
  }
}

void ArithStaticLearner::iteMinMax(TNode n, NodeBuilder<>& learned){
  Assert(n.getKind() == kind::ITE);
  Assert(n[0].getKind() != EQUAL);
  Assert(isRelationOperator(n[0].getKind()));

  TNode c = n[0];
  Kind k = oldSimplifiedKind(c);
  TNode t = n[1];
  TNode e = n[2];
  TNode cleft = (c.getKind() == NOT) ? c[0][0] : c[0];
  TNode cright = (c.getKind() == NOT) ? c[0][1] : c[1];

  if((t == cright) && (e == cleft)){
    TNode tmp = t;
    t = e;
    e = tmp;
    k = reverseRelationKind(k);
  }
  //(ite (< x y) x y)
  //(ite (x < y) x y)
  //(ite (x - y < 0) x y)
  // ----------------
  // (ite (x - y < -c) )

  if(t == cleft && e == cright){
    // t == cleft && e == cright
    Assert(t == cleft);
    Assert(e == cright);
    switch(k){
    case LT:   // (ite (< x y) x y)
    case LEQ: { // (ite (<= x y) x y)
      Node nLeqX = NodeBuilder<2>(LEQ) << n << t;
      Node nLeqY = NodeBuilder<2>(LEQ) << n << e;
      Debug("arith::static") << n << "is a min =>"  << nLeqX << nLeqY << endl;
      learned << nLeqX << nLeqY;
      ++(d_statistics.d_iteMinMaxApplications);
      break;
    }
    case GT: // (ite (> x y) x y)
    case GEQ: { // (ite (>= x y) x y)
      Node nGeqX = NodeBuilder<2>(GEQ) << n << t;
      Node nGeqY = NodeBuilder<2>(GEQ) << n << e;
      Debug("arith::static") << n << "is a max =>"  << nGeqX << nGeqY << endl;
      learned << nGeqX << nGeqY;
      ++(d_statistics.d_iteMinMaxApplications);
      break;
    }
    default: Unreachable();
    }
  }
}

void ArithStaticLearner::iteConstant(TNode n, NodeBuilder<>& learned){
  Assert(n.getKind() == ITE);

  Debug("arith::static") << "iteConstant(" << n << ")" << endl;

  if (d_minMap.find(n[1]) != d_minMap.end() && d_minMap.find(n[2]) != d_minMap.end()) {
    const DeltaRational& first = d_minMap[n[1]];
    const DeltaRational& second = d_minMap[n[2]];
    DeltaRational min = std::min(first, second);
    CDNodeToMinMaxMap::const_iterator minFind = d_minMap.find(n);
    if (minFind == d_minMap.end() || (*minFind).second < min) {
      d_minMap.insert(n, min);
      Node nGeqMin;
      if (min.getInfinitesimalPart() == 0) {
        nGeqMin = NodeBuilder<2>(kind::GEQ) << n << mkRationalNode(min.getNoninfinitesimalPart());
      } else {
        nGeqMin = NodeBuilder<2>(kind::GT) << n << mkRationalNode(min.getNoninfinitesimalPart());
      }
      learned << nGeqMin;
      Debug("arith::static") << n << " iteConstant"  << nGeqMin << endl;
      ++(d_statistics.d_iteConstantApplications);
    }
  }

  if (d_maxMap.find(n[1]) != d_maxMap.end() && d_maxMap.find(n[2]) != d_maxMap.end()) {
    const DeltaRational& first = d_maxMap[n[1]];
    const DeltaRational& second = d_maxMap[n[2]];
    DeltaRational max = std::max(first, second);
    CDNodeToMinMaxMap::const_iterator maxFind = d_maxMap.find(n);
    if (maxFind == d_maxMap.end() || (*maxFind).second > max) {
      d_maxMap.insert(n, max);
      Node nLeqMax;
      if (max.getInfinitesimalPart() == 0) {
        nLeqMax = NodeBuilder<2>(kind::LEQ) << n << mkRationalNode(max.getNoninfinitesimalPart());
      } else {
        nLeqMax = NodeBuilder<2>(kind::LT) << n << mkRationalNode(max.getNoninfinitesimalPart());
      }
      learned << nLeqMax;
      Debug("arith::static") << n << " iteConstant"  << nLeqMax << endl;
      ++(d_statistics.d_iteConstantApplications);
    }
  }
}

std::set<Node> listToSet(TNode l){
  std::set<Node> ret;
  while(l.getKind() == OR){
    Assert(l.getNumChildren() == 2);
    ret.insert(l[0]);
    l = l[1];
  }
  return ret;
}

void ArithStaticLearner::addBound(TNode n) {

  CDNodeToMinMaxMap::const_iterator minFind = d_minMap.find(n[0]);
  CDNodeToMinMaxMap::const_iterator maxFind = d_maxMap.find(n[0]);

  Rational constant = n[1].getConst<Rational>();
  DeltaRational bound = constant;

  switch(Kind k = n.getKind()) {
    case kind::LT: bound = DeltaRational(constant, -1); CVC4_FALLTHROUGH;
    case kind::LEQ:
      if (maxFind == d_maxMap.end() || (*maxFind).second > bound)
      {
        d_maxMap.insert(n[0], bound);
        Debug("arith::static") << "adding bound " << n << endl;
      }
      break;
    case kind::GT: bound = DeltaRational(constant, 1); CVC4_FALLTHROUGH;
    case kind::GEQ:
      if (minFind == d_minMap.end() || (*minFind).second < bound)
      {
        d_minMap.insert(n[0], bound);
        Debug("arith::static") << "adding bound " << n << endl;
      }
      break;
    default: Unhandled() << k; break;
  }
}

}/* CVC4::theory::arith namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */
