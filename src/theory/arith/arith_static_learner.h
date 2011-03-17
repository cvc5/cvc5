#include "cvc4_private.h"

#ifndef __CVC4__THEORY__ARITH__ARITH_STATIC_LEARNER_H
#define __CVC4__THEORY__ARITH__ARITH_STATIC_LEARNER_H


#include "util/stats.h"
#include "theory/arith/arith_utilities.h"
#include <set>

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

public:
  ArithStaticLearner();
  void staticLearning(TNode n, NodeBuilder<>& learned);

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
