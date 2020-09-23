/*********************                                                        */
/*! \file bv_inequality_graph.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Liana Hadarean, Mathias Preiner, Tim King
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Algebraic solver.
 **
 ** Algebraic solver.
 **/

#include "cvc4_private.h"

#ifndef CVC4__THEORY__BV__BV_INEQUALITY__GRAPH_H
#define CVC4__THEORY__BV__BV_INEQUALITY__GRAPH_H

#include <list>
#include <queue>
#include <unordered_map>
#include <unordered_set>

#include "context/cdqueue.h"
#include "context/context.h"
#include "theory/theory.h"
#include "theory/uf/equality_engine.h"

namespace CVC4 {
namespace theory {
namespace bv {

typedef unsigned TermId;
typedef unsigned ReasonId;
extern const TermId UndefinedTermId;
extern const ReasonId UndefinedReasonId;
extern const ReasonId AxiomReasonId;

class InequalityGraph : public context::ContextNotifyObj{

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
  
  typedef context::CDHashMap<TermId, ModelValue> ModelValues;

  struct QueueComparator {
    const ModelValues* d_model;
    QueueComparator(const ModelValues* model)
      : d_model(model)
    {}
    bool operator() (TermId left, TermId right) const {
      Assert(d_model->find(left) != d_model->end()
             && d_model->find(right) != d_model->end());

      return (*(d_model->find(left))).second.value < (*(d_model->find(right))).second.value; 
    }
  }; 

  typedef std::unordered_map<TNode, ReasonId, TNodeHashFunction> ReasonToIdMap;
  typedef std::unordered_map<TNode, TermId, TNodeHashFunction> TermNodeToIdMap;

  typedef std::vector<InequalityEdge> Edges; 
  typedef std::unordered_set<TermId> TermIdSet;

  typedef std::priority_queue<TermId, std::vector<TermId>, QueueComparator> BFSQueue; 
  typedef std::unordered_set<TNode, TNodeHashFunction> TNodeSet;
  typedef std::unordered_set<Node, NodeHashFunction> NodeSet;

  std::vector<InequalityNode> d_ineqNodes;
  std::vector< Edges > d_ineqEdges;

  // to keep the explanation nodes alive
  NodeSet d_reasonSet; 
  std::vector<TNode> d_reasonNodes;
  ReasonToIdMap d_reasonToIdMap;
  
  std::vector<Node> d_termNodes;
  TermNodeToIdMap d_termNodeToIdMap;

  context::CDO<bool> d_inConflict;
  std::vector<TNode> d_conflict;

  ModelValues  d_modelValues;
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

  Edges& getEdges(TermId id)
  {
    Assert(id < d_ineqEdges.size());
    return d_ineqEdges[id];
  }
  InequalityNode& getInequalityNode(TermId id)
  {
    Assert(id < d_ineqNodes.size());
    return d_ineqNodes[id];
  }
  const InequalityNode& getInequalityNode(TermId id) const
  {
    Assert(id < d_ineqNodes.size());
    return d_ineqNodes[id];
  }
  unsigned getBitwidth(TermId id) const { return getInequalityNode(id).getBitwidth(); }
  bool isConst(TermId id) const { return getInequalityNode(id).isConstant(); }
  
  BitVector getValue(TermId id) const; 
    
  void addEdge(TermId a, TermId b, bool strict, TermId reason);
  
  void setConflict(const std::vector<ReasonId>& conflict);
  /** 
   * If necessary update the value in the model of the current queue element. 
   * 
   * @param id current queue element we are updating
   * @param start node we started with, to detect cycles
   * 
   * @return 
   */
  bool updateValue(TermId id, ModelValue new_mv, TermId start, bool& changed);
  /** 
   * Update the current model starting with the start term. 
   * 
   * @param queue 
   * @param start 
   * 
   * @return 
   */
  bool processQueue(BFSQueue& queue, TermId start);
  /** 
   * Return the reasons why from <= to. If from is undefined we just
   * explain the current value of to. 
   * 
   * @param from 
   * @param to 
   * @param explanation 
   */
  void computeExplanation(TermId from, TermId to, std::vector<ReasonId>& explanation); 
  //  void splitDisequality(TNode diseq); 

  /**
     Disequality reasoning
   */
  
  /*** The currently asserted disequalities */
  context::CDQueue<TNode> d_disequalities;
  typedef context::CDHashSet<Node, NodeHashFunction> CDNodeSet;
  CDNodeSet d_disequalitiesAlreadySplit; 
  Node makeDiseqSplitLemma(TNode diseq); 
  /** Backtracking mechanisms **/
  std::vector<std::pair<TermId, InequalityEdge> > d_undoStack;
  context::CDO<unsigned> d_undoStackIndex;

  void contextNotifyPop() override { backtrack(); }

  void backtrack(); 

public:
  
  InequalityGraph(context::Context* c, context::Context* u, bool s = false)
    : ContextNotifyObj(c), 
      d_ineqNodes(),
      d_ineqEdges(),
      d_inConflict(c, false),
      d_conflict(),
      d_modelValues(c),
      d_disequalities(c),
      d_disequalitiesAlreadySplit(u),
      d_undoStack(),
      d_undoStackIndex(c)
  {}
  /** 
   * Add a new inequality to the graph 
   * 
   * @param a 
   * @param b 
   * @param strict 
   * @param reason 
   * 
   * @return 
   */
  bool addInequality(TNode a, TNode b, bool strict, TNode reason);
  /** 
   * Add a new disequality to the graph. This may lead in a lemma. 
   * 
   * @param a 
   * @param b 
   * @param reason 
   * 
   * @return 
   */
  bool addDisequality(TNode a, TNode b, TNode reason); 
  void getConflict(std::vector<TNode>& conflict);
  virtual ~InequalityGraph() {}
  /** 
   * Check that the currently asserted disequalities that have not been split on
   * are still true in the current model. 
   */
  void checkDisequalities(std::vector<Node>& lemmas);
  /** 
   * Return true if a < b is entailed by the current set of assertions. 
   * 
   * @param a 
   * @param b 
   * 
   * @return 
   */
  bool isLessThan(TNode a, TNode b);
  /** 
   * Returns true if the term has a value in the model (i.e. if we have seen it)
   * 
   * @param a 
   * 
   * @return 
   */
  bool hasValueInModel(TNode a) const;
  /** 
   * Return the value of a in the current model. 
   * 
   * @param a 
   * 
   * @return 
   */
  BitVector getValueInModel(TNode a) const;

  void getAllValuesInModel(std::vector<Node>& assignments); 
}; 

}
}
}

#endif /* CVC4__THEORY__BV__BV_INEQUALITY__GRAPH_H */
