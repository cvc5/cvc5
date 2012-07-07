/*********************                                                        */
/*! \file arith_static_learner.cpp
 ** \verbatim
 ** Original author: taking
 ** Major contributors: dejan
 ** Minor contributors (to current version): mdeters
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

#include "theory/rewriter.h"

#include "theory/arith/arith_utilities.h"
#include "theory/arith/arith_static_learner.h"

#include "util/propositional_query.h"

#include "expr/expr.h"
#include "expr/convenience_node_builders.h"

#include <vector>

using namespace std;
using namespace CVC4::kind;

namespace CVC4 {
namespace theory {
namespace arith {


ArithStaticLearner::ArithStaticLearner(SubstitutionMap& pbSubstitutions) :
  d_miplibTrick(),
  d_miplibTrickKeys(),
  d_pbSubstitutions(pbSubstitutions),
  d_statistics()
{}

ArithStaticLearner::Statistics::Statistics():
  d_iteMinMaxApplications("theory::arith::iteMinMaxApplications", 0),
  d_iteConstantApplications("theory::arith::iteConstantApplications", 0),
  d_miplibtrickApplications("theory::arith::miplibtrickApplications", 0),
  d_avgNumMiplibtrickValues("theory::arith::avgNumMiplibtrickValues")
{
  StatisticsRegistry::registerStat(&d_iteMinMaxApplications);
  StatisticsRegistry::registerStat(&d_iteConstantApplications);
  StatisticsRegistry::registerStat(&d_miplibtrickApplications);
  StatisticsRegistry::registerStat(&d_avgNumMiplibtrickValues);
}

ArithStaticLearner::Statistics::~Statistics(){
  StatisticsRegistry::unregisterStat(&d_iteMinMaxApplications);
  StatisticsRegistry::unregisterStat(&d_iteConstantApplications);
  StatisticsRegistry::unregisterStat(&d_miplibtrickApplications);
  StatisticsRegistry::unregisterStat(&d_avgNumMiplibtrickValues);
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

  postProcess(learned);
}


void ArithStaticLearner::clear(){
  d_miplibTrick.clear();
  d_miplibTrickKeys.clear();
  // do not clear d_pbSubstitutions, as it is shared
}


void ArithStaticLearner::process(TNode n, NodeBuilder<>& learned, const TNodeSet& defTrue){
  Debug("arith::static") << "===================== looking at " << n << endl;

  switch(n.getKind()){
  case ITE:
    if(n[0].getKind() != EQUAL &&
       isRelationOperator(n[0].getKind())  ){
      iteMinMax(n, learned);
    }

    if((d_minMap.find(n[1]) != d_minMap.end() && d_minMap.find(n[2]) != d_minMap.end()) ||
       (d_maxMap.find(n[1]) != d_maxMap.end() && d_maxMap.find(n[2]) != d_maxMap.end())) {
      iteConstant(n, learned);
    }
    break;
  case IMPLIES:
    // == 3-FINITE VALUE SET : Collect information ==
    if(n[1].getKind() == EQUAL &&
       n[1][0].getMetaKind() == metakind::VARIABLE &&
       defTrue.find(n) != defTrue.end()){
      Node eqTo = n[1][1];
      Node rewriteEqTo = Rewriter::rewrite(eqTo);
      if(rewriteEqTo.getKind() == CONST_RATIONAL){

        TNode var = n[1][0];
        if(d_miplibTrick.find(var)  == d_miplibTrick.end()){
          d_miplibTrick.insert(make_pair(var, set<Node>()));
          d_miplibTrickKeys.push_back(var);
        }
        d_miplibTrick[var].insert(n);
        Debug("arith::miplib") << "insert " << var  << " const " << n << endl;
      }
    }
    break;
  case CONST_RATIONAL:
    // Mark constants as minmax
    d_minMap[n] = n.getConst<Rational>();
    d_maxMap[n] = n.getConst<Rational>();
    break;
  case OR: {
    // Look for things like "x = 0 OR x = 1" (that are defTrue) and
    // turn them into a pseudoboolean.  We catch "x >= 0
    if(defTrue.find(n) == defTrue.end() ||
       n.getNumChildren() != 2 ||
       n[0].getKind() != EQUAL ||
       n[1].getKind() != EQUAL) {
      break;
    }
    Node var, c1, c2;
    if(n[0][0].getMetaKind() == metakind::VARIABLE &&
       n[0][1].getMetaKind() == metakind::CONSTANT) {
      var = n[0][0];
      c1 = n[0][1];
    } else if(n[0][1].getMetaKind() == metakind::VARIABLE &&
              n[0][0].getMetaKind() == metakind::CONSTANT) {
      var = n[0][1];
      c1 = n[0][0];
    } else {
      break;
    }
    if(!var.getType().isInteger() ||
       !c1.getType().isReal()) {
      break;
    }
    if(var == n[1][0]) {
      c2 = n[1][1];
    } else if(var == n[1][1]) {
      c2 = n[1][0];
    } else {
      break;
    }
    if(!c2.getType().isReal()) {
      break;
    }

    break;
  }
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
  if(t == cleft && e == cright){
    // t == cleft && e == cright
    Assert( t == cleft );
    Assert( e == cright );
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
    DeltaRational min = std::min(d_minMap[n[1]], d_minMap[n[2]]);
    NodeToMinMaxMap::iterator minFind = d_minMap.find(n);
    if (minFind == d_minMap.end() || minFind->second < min) {
      d_minMap[n] = min;
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
    DeltaRational max = std::max(d_maxMap[n[1]], d_maxMap[n[2]]);
    NodeToMinMaxMap::iterator maxFind = d_maxMap.find(n);
    if (maxFind == d_maxMap.end() || maxFind->second > max) {
      d_maxMap[n] = max;
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


void ArithStaticLearner::postProcess(NodeBuilder<>& learned){
  // == 3-FINITE VALUE SET ==
  list<TNode>::iterator keyIter = d_miplibTrickKeys.begin();
  list<TNode>::iterator endKeys = d_miplibTrickKeys.end();
  while(keyIter != endKeys) {
    TNode var = *keyIter;
    const set<Node>& imps = d_miplibTrick[var];

    Assert(!imps.empty());
    vector<Node> conditions;
    set<Rational> values;
    set<Node>::const_iterator j=imps.begin(), impsEnd=imps.end();
    for(; j != impsEnd; ++j){
      TNode imp = *j;
      Assert(imp.getKind() == IMPLIES);
      Assert(imp[1].getKind() == EQUAL);

      Node eqTo = imp[1][1];
      Node rewriteEqTo = Rewriter::rewrite(eqTo);
      Assert(rewriteEqTo.getKind() == CONST_RATIONAL);

      conditions.push_back(imp[0]);
      values.insert(rewriteEqTo.getConst<Rational>());
    }

    Node possibleTaut = Node::null();
    if(conditions.size() == 1){
      possibleTaut = conditions.front();
    }else{
      NodeBuilder<> orBuilder(OR);
      orBuilder.append(conditions);
      possibleTaut = orBuilder;
    }


    Debug("arith::miplib") << "var: " << var << endl;
    Debug("arith::miplib") << "possibleTaut: " << possibleTaut << endl;

    Result isTaut = PropositionalQuery::isTautology(possibleTaut);
    if(isTaut == Result(Result::VALID)){
      miplibTrick(var, values, learned);
      d_miplibTrick.erase(var);
      // also have to erase from keys list
      if(keyIter == endKeys) {
        // last element is special: exit loop
        d_miplibTrickKeys.erase(keyIter);
        break;
      } else {
        // non-last element: make sure iterator is incremented before erase
        list<TNode>::iterator eraseIter = keyIter++;
        d_miplibTrickKeys.erase(eraseIter);
      }
    } else {
      ++keyIter;
    }
  }
}


void ArithStaticLearner::miplibTrick(TNode var, set<Rational>& values, NodeBuilder<>& learned){

  Debug("arith::miplib") << var << " found a tautology!"<< endl;

  const Rational& min = *(values.begin());
  const Rational& max = *(values.rbegin());

  Debug("arith::miplib") << "min: " << min << endl;
  Debug("arith::miplib") << "max: " << max << endl;

  Assert(min <= max);
  ++(d_statistics.d_miplibtrickApplications);
  (d_statistics.d_avgNumMiplibtrickValues).addEntry(values.size());

  Node nGeqMin = NodeBuilder<2>(GEQ) << var << mkRationalNode(min);
  Node nLeqMax = NodeBuilder<2>(LEQ) << var << mkRationalNode(max);
  Debug("arith::miplib") << nGeqMin << nLeqMax << endl;
  learned << nGeqMin << nLeqMax;
  set<Rational>::iterator valuesIter = values.begin();
  set<Rational>::iterator valuesEnd = values.end();
  set<Rational>::iterator valuesPrev = valuesIter;
  ++valuesIter;
  for(; valuesIter != valuesEnd; valuesPrev = valuesIter, ++valuesIter){
    const Rational& prev = *valuesPrev;
    const Rational& curr = *valuesIter;
    Assert(prev < curr);

    //The interval (last,curr) can be excluded:
    //(not (and (> var prev) (< var curr))
    //<=> (or (not (> var prev)) (not (< var curr)))
    //<=> (or (<= var prev) (>= var curr))
    Node leqPrev = NodeBuilder<2>(LEQ) << var << mkRationalNode(prev);
    Node geqCurr = NodeBuilder<2>(GEQ) << var << mkRationalNode(curr);
    Node excludedMiddle =  NodeBuilder<2>(OR) << leqPrev << geqCurr;
    Debug("arith::miplib") << excludedMiddle << endl;
    learned << excludedMiddle;
  }
}

void ArithStaticLearner::addBound(TNode n) {

  NodeToMinMaxMap::iterator minFind = d_minMap.find(n[0]);
  NodeToMinMaxMap::iterator maxFind = d_maxMap.find(n[0]);

  Rational constant = n[1].getConst<Rational>();
  DeltaRational bound = constant;

  switch(Kind k = n.getKind()) {
  case kind::LT:
    bound = DeltaRational(constant, -1);
    /* fall through */
  case kind::LEQ:
    if (maxFind == d_maxMap.end() || maxFind->second > bound) {
      d_maxMap[n[0]] = bound;
      Debug("arith::static") << "adding bound " << n << endl;
    }
    break;
  case kind::GT:
    bound = DeltaRational(constant, 1);
    /* fall through */
  case kind::GEQ:
    if (minFind == d_minMap.end() || minFind->second < bound) {
      d_minMap[n[0]] = bound;
      Debug("arith::static") << "adding bound " << n << endl;
    }
    break;
  default:
    Unhandled(k);
    break;
  }
}

}/* CVC4::theory::arith namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */
