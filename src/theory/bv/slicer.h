/*********************                                                        */
/*! \file slicer.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Liana Hadarean, Mathias Preiner, Tim King
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Bitvector theory.
 **
 ** Bitvector theory.
 **/

#include "cvc4_private.h"

#include <math.h>

#include <vector>
#include <list>
#include <unordered_map>

#include "expr/node.h"
#include "theory/bv/theory_bv_utils.h"
#include "util/bitvector.h"
#include "util/index.h"
#include "util/statistics_registry.h"

#ifndef CVC4__THEORY__BV__SLICER_BV_H
#define CVC4__THEORY__BV__SLICER_BV_H


namespace CVC4 {

namespace theory {
namespace bv {



typedef Index TermId;
extern const TermId UndefinedId;


/** 
 * Base
 * 
 */
class Base {
  Index d_size;
  std::vector<uint32_t> d_repr;
public:
  Base(Index size);
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
typedef std::unordered_set<TermId> TermSet;
typedef std::vector<TermId> Decomposition; 

struct ExtractTerm {
  TermId id;
  Index high;
  Index low;
  ExtractTerm(TermId i, Index h, Index l)
    : id (i),
      high(h),
      low(l)
  {
    Assert(h >= l && id != UndefinedId);
  }
  Index getBitwidth() const { return high - low + 1; }
  std::string debugPrint() const; 
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


class UnionFind {
  class Node {
    Index d_bitwidth;
    TermId d_ch1, d_ch0;
    TermId d_repr;
  public:
    Node(Index b)
  : d_bitwidth(b),
    d_ch1(UndefinedId),
    d_ch0(UndefinedId), 
    d_repr(UndefinedId)
    {}
    
    TermId getRepr() const { return d_repr; }
    Index getBitwidth() const { return d_bitwidth; }
    bool hasChildren() const { return d_ch1 != UndefinedId && d_ch0 != UndefinedId; }

    TermId getChild(Index i) const {
      Assert(i < 2);
      return i == 0? d_ch0 : d_ch1;
    }
    void setRepr(TermId id) {
      Assert(!hasChildren());
      d_repr = id;
    }
    void setChildren(TermId ch1, TermId ch0) {
      Assert(d_repr == UndefinedId && !hasChildren());
      d_ch1 = ch1;
      d_ch0 = ch0; 
    }
    std::string debugPrint() const;
  };
  
  /// map from TermId to the nodes that represent them 
  std::vector<Node> d_nodes;
  /// a term is in this set if it is its own representative
  TermSet d_representatives;
  
  void getDecomposition(const ExtractTerm& term, Decomposition& decomp);
  void handleCommonSlice(const Decomposition& d1, const Decomposition& d2, TermId common);
  /// getter methods for the internal nodes
  TermId getRepr(TermId id)  const {
    Assert(id < d_nodes.size());
    return d_nodes[id].getRepr(); 
  }
  TermId getChild(TermId id, Index i) const {
    Assert(id < d_nodes.size());
    return d_nodes[id].getChild(i); 
  }
  Index getCutPoint(TermId id) const {
    return getBitwidth(getChild(id, 0)); 
  }
  bool hasChildren(TermId id) const {
    Assert(id < d_nodes.size());
    return d_nodes[id].hasChildren(); 
  }
  /// setter methods for the internal nodes
  void setRepr(TermId id, TermId new_repr) {
    Assert(id < d_nodes.size());
    d_nodes[id].setRepr(new_repr); 
  }
  void setChildren(TermId id, TermId ch1, TermId ch0) {
    Assert(id < d_nodes.size()
           && getBitwidth(id) == getBitwidth(ch1) + getBitwidth(ch0));
    d_nodes[id].setChildren(ch1, ch0); 
  }

  class Statistics {
  public:
    IntStat d_numNodes; 
    IntStat d_numRepresentatives;
    IntStat d_numSplits;
    IntStat d_numMerges;
    AverageStat d_avgFindDepth;
    ReferenceStat<unsigned> d_numAddedEqualities; 
    //IntStat d_numAddedEqualities; 
    Statistics();
    ~Statistics();
  };

  Statistics d_statistics
;
  
public:
  UnionFind()
    : d_nodes(),
      d_representatives()
  {}

  TermId addTerm(Index bitwidth);
  void unionTerms(const ExtractTerm& t1, const ExtractTerm& t2); 
  void merge(TermId t1, TermId t2);
  TermId find(TermId t1); 
  void split(TermId term, Index i);

  void getNormalForm(const ExtractTerm& term, NormalForm& nf);
  void alignSlicings(const ExtractTerm& term1, const ExtractTerm& term2);
  void ensureSlicing(const ExtractTerm& term);
  Index getBitwidth(TermId id) const {
    Assert(id < d_nodes.size());
    return d_nodes[id].getBitwidth(); 
  }
  std::string debugPrint(TermId id);
  friend class Slicer; 
};

class Slicer {
  std::unordered_map<TermId, TNode> d_idToNode;
  std::unordered_map<TNode, TermId, TNodeHashFunction> d_nodeToId;
  std::unordered_map<TNode, bool, TNodeHashFunction> d_coreTermCache;
  UnionFind d_unionFind;
  ExtractTerm registerTerm(TNode node); 
public:
  Slicer()
    : d_idToNode(),
      d_nodeToId(),
      d_coreTermCache(),
      d_unionFind()
  {}
  
  void getBaseDecomposition(TNode node, std::vector<Node>& decomp);
  void processEquality(TNode eq);
  bool isCoreTerm (TNode node);
  static void splitEqualities(TNode node, std::vector<Node>& equalities);
  static unsigned d_numAddedEqualities; 
}; 


}/* CVC4::theory::bv namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */

#endif /* CVC4__THEORY__BV__SLICER_BV_H */
