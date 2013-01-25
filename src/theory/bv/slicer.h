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

#include "expr/node.h"
#include "theory/bv/theory_bv_utils.h"
#ifndef __CVC4__THEORY__BV__SLICER_BV_H
#define __CVC4__THEORY__BV__SLICER_BV_H


namespace CVC4 {

namespace theory {
namespace bv {

typedef uint32_t TermId;
typedef uint32_t Index;



/** 
 * Base
 * 
 */
class Base {
  Index d_size;
  std::vector<uint32_t> d_repr;
public:
  Base(uint32_t size);
  void sliceAt(Index index); 
  void sliceWith(const Base& other);
  bool isCutPoint(Index index) const;
  void diffCutPoints(const Base& other, Base& res) const;
  bool isEmpty() const;
  std::string debugPrint() const;
}; 

/**
 * UnionFind
 * 
 */
typedef __gnu_cxx::hash_set<TermId> TermSet;
typedef std::vector<TermId> Decomposition; 

struct ExtractTerm {
  TermId id;
  Index high;
  Index low;
  ExtractTerm(TermId i, Index h, Index l)
    : id (i)
      high(h)
      low(l)
  {
    Assert (h >= l && id != -1); 
  }
};

struct NormalForm {
  Base base;
  Decomposition decomp;
  NormalForm(Index bitwidth)
    : base(bitwidth),
      decomp()
  {}
};


class UnionFind {
  class Node {
    TermId d_repr;
    TermId d_ch1, d_ch2;
    Index d_bitwidth;
  public:
    Node(Index b)
  : d_bitwidth(b),
    d_ch1(-1),
    d_ch2(-1), 
    d_repr(-1)
    {}
    
    TermId getRepr() const { return d_repr; }
    Index getBitwidth() const { return d_bitwidth; }
    bool hasChildren() const { return d_ch1 != -1 && d_ch2 != -1; }

    TermId getChild(Index i) const {
      Assert (i < 2);
      return i == 0? ch1 : ch2;
    }
    Index getCutPoint() const {
      Assert (d_ch1 != -1 && d_ch2 != -1);
      return getNode(d_ch1).getBitwidth(); 
    }
    void setRepr(TermId id) {
      Assert (d_children.empty());
      d_repr = id;
    }

    void setChildren(TermId ch1, TermId ch2) {
      Assert (d_repr == -1 && d_children.empty());
      markAsNotTopLevel(ch1);
      markAsNotTopLevel(ch2); 
      d_children.push_back(ch1);
      d_children.push_back(ch2); 
    }
    
    // void setChildren(TermId ch1, TermId ch2, TermId ch3) {
    //   Assert (d_repr == -1 && d_children.empty());
    //   d_children.push_back(ch1);
    //   d_children.push_back(ch2);
    //   d_children.push_back(ch3); 
    // }
    
  };

  std::vector<Node> d_nodes;

  TermSet d_representatives;
  TermSet d_topLevelTerms;
  void markAsNotTopLevel(TermId id) {
    if (d_topLevelTerms.find(id) != d_topLevelTerms.end())
      d_topLevelTerms.erase(id); 
  }

  bool isTopLevel(TermId id) {
    return d_topLevelTerms.find(id) != d_topLevelTerms.end(); 
  }
  
  Index getBitwidth(TermId id) {
    Assert (id < d_nodes.size());
    return d_nodes[id].getBitwidth(); 
  }
  
public:
  UnionFind()
    : d_nodes(),
      d_representatives()
  {}

  TermId addTerm(Index bitwidth);
  void merge(TermId t1, TermId t2);
  TermId find(TermId t1); 
  TermId split(TermId term, Index i);

  void getNormalForm(ExtractTerm term, NormalForm& nf);
  void alignSlicings(NormalForm& nf1, NormalForm& nf2);

  Node getNode(TermId id) {
    Assert (id < d_nodes.size());
    return d_nodes[id]; 
  }
};

class Slicer {
  __gnu_cxx::hash_map<TermId, TNode> d_idToNode;
  __gnu_cxx::hash_map<TNode, TermId> d_nodeToId;
  UnionFind d_unionFind();
 
public:
  Slicer()
    : d_topLevelTerms(),
      d_unionFind()
  {}
  
  void getBaseDecomposition(TNode node, std::vector<Node>& decomp) const;
  void processEquality(TNode eq);
}; 

}/* CVC4::theory::bv namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */

#endif /* __CVC4__THEORY__BV__SLICER_BV_H */
