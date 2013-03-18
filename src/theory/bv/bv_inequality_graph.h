/*********************                                                        */
/*! \file bv_inequality_graph.h
 ** \verbatim
 ** Original author: lianah
 ** Major contributors: none
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009-2012  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief Algebraic solver. 
 **
 ** Algebraic solver.
 **/

#include "cvc4_private.h"

#ifndef __CVC4__THEORY__BV__BV_INEQUALITY__GRAPH_H
#define __CVC4__THEORY__BV__BV_INEQUALITY__GRAPH_H

#include "context/context.h"
#include "context/cdqueue.h"
#include "theory/uf/equality_engine.h"
#include "theory/theory.h"

namespace CVC4 {
namespace theory {


namespace bv {

typedef unsigned TermId; 
typedef unsigned ReasonId;

class InequalityGraph {
  context::Context d_context;

  struct InequalityEdge {
    TermId next;
    ReasonId reason;
    InequalityEdge(TermId n, ReasonId r)
      : next(n)
        reason(r)
    {}
  };
  
  class InequalityNode {
    TermId d_id;
    unsigned d_bitwidth;
    bool d_isConstant;
    BitVector d_value;
  };
  std::vector<InequalityNode> d_nodes;
  std::vector< std::vector<InequalityEdge> > d_nodeEdges;
  
public:
  
  InequalityGraph(context::Context* c)
    : d_context(c)
  {}
  bool addInequality(TermId a, TermId b, ReasonId reason);
  bool propagate();
  bool areLessThan(TermId a, TermId b);
  void getConflict(std::vector<ReasonId>& conflict);
  TermId addTerm(unsigned bitwidth);
  TermId addTerm(const BitVector& value); 
}; 

}
}
}

#endif /* __CVC4__THEORY__BV__BV_INEQUALITY__GRAPH_H */
