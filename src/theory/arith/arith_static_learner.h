/*********************                                                        */
/*! \file arith_static_learner.h
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

#include "cvc4_private.h"

#ifndef __CVC4__THEORY__ARITH__ARITH_STATIC_LEARNER_H
#define __CVC4__THEORY__ARITH__ARITH_STATIC_LEARNER_H


#include "util/stats.h"
#include "theory/arith/arith_utilities.h"
#include <set>
#include <list>

namespace CVC4 {
namespace theory {
namespace arith {

class ArithStaticLearner {
private:
  typedef __gnu_cxx::hash_set<TNode, TNodeHashFunction> TNodeSet;

  /* Maps a variable, x, to the set of defTrue nodes of the form
   *  (=> _ (= x c))
   * where c is a constant.
   */
  typedef __gnu_cxx::hash_map<Node, std::set<Node>, NodeHashFunction> VarToNodeSetMap;
  VarToNodeSetMap d_miplibTrick;
  std::list<TNode> d_miplibTrickKeys;

  /**
   * Map from a node to it's minimum and maximum.
   */
  typedef __gnu_cxx::hash_map<Node, DeltaRational, NodeHashFunction> NodeToMinMaxMap;
  NodeToMinMaxMap d_minMap;
  NodeToMinMaxMap d_maxMap;

public:
  ArithStaticLearner();
  void staticLearning(TNode n, NodeBuilder<>& learned);

  void addBound(TNode n);

  void clear();

private:
  void process(TNode n, NodeBuilder<>& learned, const TNodeSet& defTrue);

  void postProcess(NodeBuilder<>& learned);

  void iteMinMax(TNode n, NodeBuilder<>& learned);
  void iteConstant(TNode n, NodeBuilder<>& learned);

  void miplibTrick(TNode var, std::set<Rational>& values, NodeBuilder<>& learned);

  /** These fields are designed to be accessable to ArithStaticLearner methods. */
  class Statistics {
  public:
    IntStat d_iteMinMaxApplications;
    IntStat d_iteConstantApplications;

    IntStat d_miplibtrickApplications;
    AverageStat d_avgNumMiplibtrickValues;

    Statistics();
    ~Statistics();
  };

  Statistics d_statistics;

};/* class ArithStaticLearner */

}/* CVC4::theory::arith namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */

#endif /* __CVC4__THEORY__ARITH__ARITH_STATIC_LEARNER_H */
