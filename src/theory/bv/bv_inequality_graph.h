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


  context::Context* d_context;

  struct InequalityEdge {
    TermId next;
    ReasonId reason;
    InequalityEdge(TermId n, ReasonId r)
      : next(n), 
        reason(r)
    {}
  };
  
  class InequalityNode {
    TermId d_id;
    unsigned d_bitwidth;
    bool d_isConstant;
    BitVector d_value;
  public:
    InequalityNode(TermId id, unsigned bitwidth, bool isConst = false)
      : d_id(id),
        d_bitwidth(bitwidth),
        d_isConstant(isConst),
        d_value(BitVector(bitwidth, 0u))
    {}
    TermId getId() const { return d_id; }
    unsigned getBitwidth() const { return d_bitwidth; }
    bool isConstant() const { return d_isConstant; }
    const BitVector& getValue() const { return d_value; }
  };

  struct PQueueElement {
    TermId id;
    BitVector min_value;
    PQueueElement(TermId id, BitVector min)
      : id(id), 
        min_value(min)
    {}
    bool operator< (const PQueueElement& other) const {
      return min_value < other.min_value; 
    }
  }; 
  
  typedef __gnu_cxx::hash_map<TNode, ReasonId, TNodeHashFunction> ReasonToIdMap;
  typedef __gnu_cxx::hash_map<TNode, TermId, TNodeHashFunction> TermNodeToIdMap;

  typedef std::vector<InequalityEdge> Edges; 
  typedef __gnu_cxx::hash_set<TermId> TermIdSet;

  typedef std::queue<PQueueElement> BFSQueue;

  
  std::vector<InequalityNode> d_ineqNodes;

  std::vector< Edges > d_ineqEdges;
  std::vector< Edges > d_parentEdges;
  
  std::vector<TNode> d_reasonNodes;
  std::vector<TNode> d_termNodes;
  ReasonToIdMap d_reasonToIdMap; 
  TermNodeToIdMap d_termNodeToIdMap;

  TermId registerTerm(TNode term);
  ReasonId registerReason(TNode reason);
  TNode getReason(ReasonId id) const;
  TNode getTerm(TermId id) const; 

  Edges& getOutEdges(TermId id) { Assert (id < d_ineqEdges.size()); return d_ineqEdges[id]; }
  Edges& getInEdges(TermId id) { Assert (id < d_parentEdges.size()); return d_parentEdges[id]; }
  InequalityNode& getInequalityNode(TermId id) { Assert (id < d_ineqNodes.size()); return d_ineqNodes[id]; }
  const BitVector& getValue(TermId id) const { return getInequalityNode().getValue(); }
  bool addInequalityInternal(TermId a, TermId b, ReasonId reason);
  bool areLessThanInternal(TermId a, TermId b);
  void getConflictInternal(std::vector<ReasonId>& conflict);

  context::CDO<bool> d_inConflict;
  context::CDList<TNode> d_conflict;
  void setConflict(const std::vector<ReasonId>& conflict); 
public:
  
  InequalityGraph(context::Context* c)
    : d_context(c),
      d_ineqNodes(),
      d_ineqEdges(),
      d_parentEdges(),
      d_inConflict(c, false),
      d_conflict(c)
  {}
  bool addInequality(TNode a, TNode b, TNode reason);
  bool areLessThan(TNode a, TNode b);
  void getConflict(std::vector<TNode>& conflict);
}; 

}
}
}

#endif /* __CVC4__THEORY__BV__BV_INEQUALITY__GRAPH_H */
