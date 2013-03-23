/*********************                                                        */
/*! \file slicer.h
 ** \verbatim
 ** Original author: lianah
 ** Major contributors: none
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010, 2011  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief Bitvector theory.
 **
 ** Bitvector theory.
 **/

#include "cvc4_private.h"


#include <vector>
#include <list>
#include <ext/hash_map>
#include <math.h>

#include "util/bitvector.h"
#include "util/statistics_registry.h"
#include "util/index.h"
#include "expr/node.h"
#include "theory/bv/theory_bv_utils.h"
#include "context/context.h"
#include "context/cdhashset.h"
#include "context/cdo.h"
#include "context/cdqueue.h"
#ifndef __CVC4__THEORY__BV__SLICER_BV_H
#define __CVC4__THEORY__BV__SLICER_BV_H


namespace CVC4 {

namespace theory {
namespace bv {



typedef Index TermId;
typedef TermId ExplanationId; 
extern const TermId UndefinedId;

class CDBase; 

/** 
 * Base
 * 
 */
class Base {
  Index d_size;
  std::vector<uint32_t> d_repr;
  void undoSliceAt(Index index); 
public:
  Base (Index size);
  void sliceAt(Index index);
  
  void sliceWith(const Base& other);
  bool isCutPoint(Index index) const;
  void diffCutPoints(const Base& other, Base& res) const;
  bool isEmpty() const;
  std::string debugPrint() const;
  Index getBitwidth() const { return d_size; }
  void clear() {
    for (unsigned i = 0; i < d_repr.size(); ++i) {
      d_repr[i] = 0; 
    }
  }
  bool operator==(const Base& other) const {
    if (other.getBitwidth() != getBitwidth())
      return false;
    for (unsigned i = 0; i < d_repr.size(); ++i) {
      if (d_repr[i] != other.d_repr[i])
        return false;
    }
    return true; 
  }
}; 


/**
 * UnionFind
 * 
 */
typedef context::CDHashSet<uint32_t, std::hash<uint32_t> > CDTermSet;
typedef std::vector<TermId> Decomposition; 

struct ExtractTerm {
  TermId id;
  Index high;
  Index low;
  ExtractTerm()
    : id (UndefinedId),
      high(UndefinedId),
      low(UndefinedId)
  {}
  ExtractTerm(TermId i, Index h, Index l)
    : id (i),
      high(h),
      low(l)
  {
    Assert (h >= l && id != UndefinedId); 
  }
  bool operator== (const ExtractTerm& other) const {
    return id == other.id && high == other.high && low == other.low; 
  }
  Index getBitwidth() const { return high - low + 1; }
  std::string debugPrint() const; 
  friend class ExtractTermHashFunction; 
};

struct ExtractTermHashFunction {
  ::std::size_t operator() (const ExtractTerm& t) const {
    __gnu_cxx::hash<unsigned> h;
    unsigned id = t.id;
    unsigned high = t.high;
    unsigned low = t.low; 
    return (h(id) * 7919 + h(high))* 4391 + h(low); 
  }
}; 

class UnionFind; 

struct NormalForm {
  Base base;
  Decomposition decomp;

  NormalForm(Index bitwidth)
    : base(bitwidth),
      decomp()
  {}
  /** 
   * Returns the term in the decomposition on which the index i
   * falls in
   * @param i 
   * 
   * @return 
   */
  std::pair<TermId, Index> getTerm(Index i, const UnionFind& uf) const;
  std::string debugPrint(const UnionFind& uf) const;
  void clear() { base.clear(); decomp.clear(); }
};

class Slicer; 

class UnionFind : public context::ContextNotifyObj {

  struct ReprEdge {
    TermId repr;
    ExplanationId reason;
    ReprEdge()
      : repr(UndefinedId),
        reason(UndefinedId)
    {}
  }; 
    
  class EqualityNode {
    Index d_bitwidth;  
    TermId d_ch1, d_ch0; // the ids of the two children if they exist
    ReprEdge d_edge;     // points to the representative and stores the explanation
    
  public:
    EqualityNode(Index b)
  : d_bitwidth(b),
    d_ch1(UndefinedId),
    d_ch0(UndefinedId), 
    d_edge()
    {}

    TermId getRepr() const { return d_edge.repr; }
    ExplanationId getReason() const { return d_edge.reason; }
    Index getBitwidth() const { return d_bitwidth; }
    bool hasChildren() const { return d_ch1 != UndefinedId && d_ch0 != UndefinedId; }

    TermId getChild(Index i) const {
      Assert (i < 2);
      return i == 0? d_ch0 : d_ch1;
    }
    void setRepr(TermId repr, ExplanationId reason) {
      Assert (! hasChildren());
      d_edge.repr = repr;
      d_edge.reason = reason; 
    }
    void setChildren(TermId ch1, TermId ch0) {
      d_ch1 = ch1;
      d_ch0 = ch0; 
    }
    std::string debugPrint() const;
  };

  // the equality nodes in the union find
  std::vector<EqualityNode> d_equalityNodes;
  
  /// getter methods for the internal nodes
  TermId getRepr(TermId id)  const;
  ExplanationId getReason(TermId id) const;
  TermId getChild(TermId id, Index i) const;
  Index getCutPoint(TermId id) const;
  bool hasChildren(TermId id) const;
  
  /// setter methods for the internal nodes
  void setRepr(TermId id, TermId new_repr, ExplanationId reason);
  void setChildren(TermId id, TermId ch1, TermId ch0); 

  // the mappings between ExtractTerms and ids
  __gnu_cxx::hash_map<TermId, ExtractTerm, __gnu_cxx::hash<TermId> > d_idToExtract;
  __gnu_cxx::hash_map<ExtractTerm, TermId, ExtractTermHashFunction > d_extractToId;

  __gnu_cxx::hash_set<TermId> d_topLevelIds;
  
  void getDecomposition(const ExtractTerm& term, Decomposition& decomp);
  void getDecompositionWithExplanation(const ExtractTerm& term, Decomposition& decomp, std::vector<ExplanationId>& explanation);
  void handleCommonSlice(const Decomposition& d1, const Decomposition& d2, TermId common);
  
  /* Backtracking mechanisms */

  enum OperationKind {
    MERGE,
    SPLIT
  }; 

  struct Operation {
    OperationKind op;
    TermId id;
    Operation(OperationKind o, TermId i)
      : op(o), id(i) {}
  };

  std::vector<Operation> d_undoStack;
  context::CDO<unsigned> d_undoStackIndex;

  void backtrack();
  void undoMerge(TermId id);
  void undoSplit(TermId id); 
  void recordOperation(OperationKind op, TermId term);
  virtual ~UnionFind() throw(AssertionException) {}
  class Statistics {
  public:
    IntStat d_numNodes; 
    IntStat d_numRepresentatives;
    IntStat d_numSplits;
    IntStat d_numMerges;
    AverageStat d_avgFindDepth;
    ReferenceStat<unsigned> d_numAddedEqualities; 
    Statistics();
    ~Statistics();
  };
  Statistics d_statistics;
  Slicer* d_slicer;
  TermId d_termIdCount; 

  TermId mkEqualityNode(Index bitwidth);
  ExtractTerm mkExtractTerm(TermId id, Index high, Index low); 
  void storeExtractTerm(Index id, const ExtractTerm& term);
  ExtractTerm getExtractTerm(TermId id) const;
  bool extractHasId(const ExtractTerm& ex) const { return d_extractToId.find(ex) != d_extractToId.end(); }
  TermId getExtractId(const ExtractTerm& ex) const {Assert (extractHasId(ex)); return d_extractToId.find(ex)->second; }
  bool isExtractTerm(TermId id) const; 
public:
  UnionFind(context::Context* ctx, Slicer* slicer)
    : ContextNotifyObj(ctx), 
      d_equalityNodes(),
      d_idToExtract(),
      d_extractToId(),
      d_topLevelIds(),
      d_undoStack(),
      d_undoStackIndex(ctx),
      d_statistics(),
      d_slicer(slicer),
      d_termIdCount(0)
  {}

  TermId addEqualityNode(unsigned bitwidth, TermId id, Index high, Index low);
  TermId registerTopLevelTerm(Index bitwidth);  
  void unionTerms(TermId id1, TermId id2, TermId reason); 
  void merge(TermId t1, TermId t2, TermId reason);
  TermId find(TermId t1);
  TermId findWithExplanation(TermId id, std::vector<ExplanationId>& explanation); 
  void split(TermId term, Index i);
  void getNormalForm(const ExtractTerm& term, NormalForm& nf);
  void getNormalFormWithExplanation(const ExtractTerm& term, NormalForm& nf, std::vector<ExplanationId>& explanation); 
  void alignSlicings(TermId id1, TermId id2);
  void ensureSlicing(TermId id);
  Index getBitwidth(TermId id) const {
    Assert (id < d_equalityNodes.size());
    return d_equalityNodes[id].getBitwidth(); 
  }
  void getBase(TermId id, Base& base, Index offset); 
  std::string debugPrint(TermId id);

  void contextNotifyPop() {
    backtrack();
  }
  friend class Slicer; 
};

class CoreSolver; 

class Slicer {
  __gnu_cxx::hash_map<TermId, TNode> d_idToNode; 
  __gnu_cxx::hash_map<TNode, TermId, TNodeHashFunction> d_nodeToId;
  __gnu_cxx::hash_map<TNode, bool, TNodeHashFunction> d_coreTermCache;
  __gnu_cxx::hash_map<TNode, ExplanationId, NodeHashFunction> d_explanationToId;
  std::vector<TNode> d_explanations; 
  UnionFind d_unionFind;

  context::CDQueue<Node> d_newSplits;
  context::CDO<unsigned>  d_newSplitsIndex;
  CoreSolver* d_coreSolver;
  TermId registerTopLevelTerm(TNode node); 
  bool isTopLevelNode(TermId id) const; 
  TermId registerTerm(TNode node);
public:
  Slicer(context::Context* ctx, CoreSolver* coreSolver)
    : d_idToNode(),
      d_nodeToId(),
      d_coreTermCache(),
      d_explanationToId(),
      d_explanations(), 
      d_unionFind(ctx, this),
      d_newSplits(ctx),
      d_newSplitsIndex(ctx, 0),
      d_coreSolver(coreSolver)
  {}
  
  void getBaseDecomposition(TNode node, std::vector<Node>& decomp, std::vector<TNode>& explanation);
  void registerEquality(TNode eq);

  void processEquality(TNode eq);
  void assertEquality(TNode eq);
  bool isCoreTerm (TNode node);

  bool hasNode(TermId id) const; 
  Node  getNode(TermId id) const;

  bool hasExplanation(ExplanationId id) const;
  TNode getExplanation(ExplanationId id) const;
  ExplanationId getExplanationId(TNode reason) const;
  
  bool termInEqualityEngine(TermId id); 
  void enqueueSplit(TermId id, Index i, TermId top, TermId bottom);
  void getNewSplits(std::vector<Node>& splits);
  static void splitEqualities(TNode node, std::vector<Node>& equalities);
  static unsigned d_numAddedEqualities;
}; 


}/* CVC4::theory::bv namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */

#endif /* __CVC4__THEORY__BV__SLICER_BV_H */
