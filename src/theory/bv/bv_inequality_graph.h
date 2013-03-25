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
#include <queue>
#include <list>
namespace CVC4 {
namespace theory {


namespace bv {

typedef unsigned TermId; 
typedef unsigned ReasonId;
extern const TermId UndefinedTermId;
extern const ReasonId UndefinedReasonId;
extern const ReasonId AxiomReasonId; 

class InequalityGraph : public context::ContextNotifyObj{


  context::Context* d_context;

  struct InequalityEdge {
    TermId next;
    ReasonId reason;
    bool strict;
    InequalityEdge(TermId n, bool s, ReasonId r)
      : next(n),
        reason(r),
        strict(s)
    {}
    bool operator==(const InequalityEdge& other) const {
      return next == other.next && reason == other.reason && strict == other.strict; 
    }
  };

  class InequalityNode {
    TermId d_id;
    unsigned d_bitwidth;
    bool d_isConstant;
  public:
    InequalityNode(TermId id, unsigned bitwidth, bool isConst)
      : d_id(id),
        d_bitwidth(bitwidth),
        d_isConstant(isConst)
    {}
    TermId getId() const { return d_id; }
    unsigned getBitwidth() const { return d_bitwidth; }
    bool isConstant() const { return d_isConstant; }
  };

  struct ModelValue {
    TermId parent;
    ReasonId reason;
    BitVector value; 
    ModelValue()
      : parent(UndefinedTermId),
        reason(UndefinedReasonId),
        value(0, 0u)
    {}
    
    ModelValue(const BitVector& val, TermId p, ReasonId r)
      : parent(p),
        reason(r),
        value(val)
    {}
  };

  struct PQueueElement {
    TermId id;
    BitVector lower_bound;
    ModelValue model_value; 
    PQueueElement(TermId id, const BitVector& lb, const ModelValue& mv)
      : id(id),
        lower_bound(lb),
        model_value(mv)
    {}
    
    bool operator< (const PQueueElement& other) const {
      return model_value.value > other.model_value.value;
    }
    std::string toString() const; 
  };
  
  typedef __gnu_cxx::hash_map<TNode, ReasonId, TNodeHashFunction> ReasonToIdMap;
  typedef __gnu_cxx::hash_map<TNode, TermId, TNodeHashFunction> TermNodeToIdMap;

  typedef std::vector<InequalityEdge> Edges; 
  typedef __gnu_cxx::hash_set<TermId> TermIdSet;

  typedef std::priority_queue<PQueueElement> BFSQueue; 
  typedef __gnu_cxx::hash_set<TNode, TNodeHashFunction> TNodeSet; 
  std::vector<InequalityNode> d_ineqNodes;
  std::vector< Edges > d_ineqEdges;
  
  std::vector<TNode> d_reasonNodes;
  ReasonToIdMap d_reasonToIdMap;
  
  std::vector<Node> d_termNodes;
  TermNodeToIdMap d_termNodeToIdMap;

  context::CDO<bool> d_inConflict;
  std::vector<TNode> d_conflict;
  bool d_signed; 

  context::CDHashMap<TermId, ModelValue>  d_modelValues;
  void initializeModelValue(TNode node); 
  void setModelValue(TermId term, const ModelValue& mv);
  ModelValue getModelValue(TermId term) const;
  bool hasModelValue(TermId id) const; 
  bool hasReason(TermId id) const; 
  
  /** 
   * Registers the term by creating its corresponding InequalityNode
   * and adding the min <= term <= max default edges. 
   * 
   * @param term 
   * 
   * @return 
   */
  TermId registerTerm(TNode term);
  TNode getTermNode(TermId id) const; 
  TermId getTermId(TNode node) const;
  bool isRegistered(TNode term) const; 
  
  ReasonId registerReason(TNode reason);
  TNode getReasonNode(ReasonId id) const;
  
  
  Edges& getEdges(TermId id) { Assert (id < d_ineqEdges.size()); return d_ineqEdges[id]; }
  InequalityNode& getInequalityNode(TermId id) { Assert (id < d_ineqNodes.size()); return d_ineqNodes[id]; }
  const InequalityNode& getInequalityNode(TermId id) const { Assert (id < d_ineqNodes.size()); return d_ineqNodes[id]; }
  unsigned getBitwidth(TermId id) const { return getInequalityNode(id).getBitwidth(); }
  bool isConst(TermId id) const { return getInequalityNode(id).isConstant(); }
  
  BitVector getValue(TermId id) const; 
    
  void addEdge(TermId a, TermId b, bool strict, TermId reason);
  
  void setConflict(const std::vector<ReasonId>& conflict);
  /** 
   * If necessary update the value in the model of the current queue element. 
   * 
   * @param el current queue element we are updating
   * @param start node we started with, to detect cycles
   * @param seen 
   * 
   * @return 
   */
  bool updateValue(const PQueueElement& el, TermId start, const TermIdSet& seen, bool& changed);
  /** 
   * Update the current model starting with the start term. 
   * 
   * @param queue 
   * @param start 
   * @param seen 
   * 
   * @return 
   */
  bool computeValuesBFS(BFSQueue& queue, TermId start, TermIdSet& seen);
  /** 
   * Return the reasons why from <= to. If from is undefined we just
   * explain the current value of to. 
   * 
   * @param from 
   * @param to 
   * @param explanation 
   */
  void computeExplanation(TermId from, TermId to, std::vector<ReasonId>& explanation); 
  void splitDisequality(TNode diseq); 

  /**
     Disequality reasoning
   */
  
  /*** The currently asserted disequalities */
  context::CDQueue<TNode> d_disequalities;
  context::CDQueue<Node> d_lemmaQueue; 
  context::CDO<unsigned> d_lemmaIndex; 
  TNodeSet d_lemmasAdded; 
  
  /** Backtracking mechanisms **/
  std::vector<std::pair<TermId, InequalityEdge> > d_undoStack;
  context::CDO<unsigned> d_undoStackIndex; 
  
  void contextNotifyPop() {
    backtrack();
  }

  void backtrack(); 

public:
  
  InequalityGraph(context::Context* c, bool s = false)
    : ContextNotifyObj(c), 
      d_context(c),
      d_ineqNodes(),
      d_ineqEdges(),
      d_inConflict(c, false),
      d_conflict(),
      d_signed(s),
      d_modelValues(c),
      d_disequalities(c),
      d_lemmaQueue(c),
      d_lemmaIndex(c, 0),
      d_lemmasAdded(),
      d_undoStack(),
      d_undoStackIndex(c)
  {}
  /** 
   * 
   * 
   * @param a 
   * @param b 
   * @param diff 
   * @param reason 
   * 
   * @return 
   */
  bool addInequality(TNode a, TNode b, bool strict, TNode reason);
  bool addDisequality(TNode a, TNode b, TNode reason); 
  bool areLessThan(TNode a, TNode b);
  void getConflict(std::vector<TNode>& conflict);
  virtual ~InequalityGraph() throw(AssertionException) {}
  void getNewLemmas(std::vector<TNode>& new_lemmas);
}; 

}
}
}

#endif /* __CVC4__THEORY__BV__BV_INEQUALITY__GRAPH_H */
