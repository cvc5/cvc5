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
#include "util/bitvector.h"
#include "expr/node.h"
#include "theory/bv/theory_bv_utils.h"
#ifndef __CVC4__THEORY__BV__SLICER_BV_H
#define __CVC4__THEORY__BV__SLICER_BV_H


namespace CVC4 {

namespace theory {
namespace bv {

typedef uint32_t RootId;
typedef uint32_t SplinterId;
typedef uint32_t Index;

class Base {
  uint32_t d_size;
  CVC4::BitVector d_repr;  
public:
  Base(uint32_t size) 
    : d_size(size) {
    Assert (size > 0);
    d_repr = BitVector(size - 1, 0u);
  }

  Base(const BitVector& repr) 
    : d_size(repr.getSize() + 1),
      d_repr(repr) {
    Assert (d_size > 0);
  }
  
  /** 
   * Marks the base by adding a cut between index and index + 1
   * 
   * @param index 
   */
  void sliceAt(Index index) {
    Assert (index < d_size - 1); 
    d_repr = d_repr.setBit(index); 
  }

  void sliceWith(const Base& other) {
    Assert (d_size == other.d_size); 
    d_repr = d_repr | other.d_repr; 
  }

  void decomposeNode(TNode node, std::vector<Node>& decomp);

  bool isCutPoint (Index index) {
    Assert (index < d_size); 
    // the last cut point is implicit
    if (index == d_size - 1)
      return true; 
    return d_repr.isBitSet(index); 
  }

  Base diffCutPoints(const Base& other) const {
    return Base(other.d_repr ^ d_repr); 
  }

  bool operator==(const Base& other) const {
    return d_repr == other.d_repr; 
  }
  bool operator!=(const Base& other) const {
    return !(*this == other); 
  }
  std::string debugPrint() {
    std::ostringstream os;
    os << "[";
    bool first = true; 
    for (Index i = 0; i < d_size - 1; ++i) {
      if (isCutPoint(i)) {
        if (first)
          first = false;
        else
          os <<"| "; 
        
        os << i ; 
      }
    }
    os << "]"; 
    return os.str(); 
  }
  
}; 


struct SplinterPointer {
  RootId term;
  uint32_t row; 
  Index index;

  SplinterPointer()
    : term(-1),
      row(-1),
      index(-1)
  {}

  SplinterPointer(RootId t, uint32_t r,  Index i)
    : term(t),
      row(r),
      index(i)
  {}
  
  bool operator==(const SplinterPointer& other) const {
    return term == other.term && index == other.index && row == other.row; 
  }
  bool operator!=(const SplinterPointer& other) const {
    return !(*this == other); 
  }

  std::string debugPrint() {
    std::ostringstream os;
    os << "(id" << term << ", row" << row <<", i" << index << ")";
    return os.str();
  }
  
};

static const SplinterPointer Undefined = SplinterPointer(-1, -1, -1); 

class Splinter {
  // start and end indices in slice
  Index d_low;
  Index d_high;

  // keeps track of splinter this splinter is equal to
  // equal to Undefined if there is none
  SplinterPointer d_pointer;
  
public:
  Splinter(uint32_t high, uint32_t low) :
    d_low(low),
    d_high(high),
    d_pointer(Undefined)
  {
    Assert (high >= low); 
  }
    
  void setPointer(const SplinterPointer& pointer) {
    Assert (d_pointer == Undefined);
    d_pointer = pointer; 
  }

  const SplinterPointer& getPointer() const {
    return d_pointer; 
  }

  Index getLow() const { return d_low; }
  Index getHigh() const {return d_high; }
  uint32_t getBitwidth() const { return d_high - d_low; }
};

class Slice {
  uint32_t d_bitwidth; 
  // map from the beginning of a splinter to the actual splinter id
  std::map<Index, Splinter*> d_splinters;
  Base d_base;
  
public:
  Slice(uint32_t bitwidth)
    : d_bitwidth(bitwidth),
      d_splinters(),
      d_base(bitwidth)
  {}
  /** 
   * Split the slice by adding a cut point between indices i and i+1
   * 
   * @param i index where to cut
   * @param id the id of the root term this slice belongs to
   * @param row the row of the SliceBlock this Slice belongs to
   */
  void split(Index i, SplinterPointer& sp, Splinter*& low_splinter, Splinter*& top_splinter);
  /** 
   * Add splinter sp at Index i. If a splinter already exists there
   * replace it and free the memory it occupied. 
   * 
   * @param i index where splinter starts
   * @param sp new splinter
   */
  void addSplinter(Index i, Splinter* sp); 
  /** 
   * Return the splinter starting at Index start.
   * 
   * @param start 
   * 
   * @return 
   */
  Splinter* getSplinter (Index start) {
    Assert (d_splinters.find(start) != d_splinters.end()); 
    return d_splinters[start]; 
  }
  const Base& getBase() const { return d_base; }

  typedef std::map<Index, Splinter*>::const_iterator const_iterator; 
  std::map<Index, Splinter*>::const_iterator begin() {
    return d_splinters.begin(); 
  }
  std::map<Index, Splinter*>::const_iterator end() {
    return d_splinters.end(); 
  }
  std::string debugPrint();
  bool isConsistent();
};

class Slicer; 

class SliceBlock {
  uint32_t d_bitwidth; 
  RootId d_rootId;                /**< the id of the root term this block corresponds to */
  std::vector<Slice*> d_block;    /**< the slices in the block */
  Base d_base;                    /**<  the base corresponding to this block containing all the cut points.
                                   Invariant: the base should contain all the cut-points in the slices*/
  Slicer* d_slicer; // FIXME: more elegant way to do this

public:


  SliceBlock(RootId rootId, uint32_t bitwidth, Slicer* slicer)
    : d_bitwidth(bitwidth),
      d_rootId(rootId),
      d_block(),
      d_base(bitwidth),
      d_slicer(slicer)
  {}

  uint32_t addSlice(Slice* slice) {
    // update the base with the cut-points in the slice
    Debug("bv-slice") << "SliceBlock::addSlice Block"<< d_rootId << " adding slice " << slice->debugPrint() << std::endl; 
    d_base.sliceWith(slice->getBase()); 
    d_block.push_back(slice);
    return d_block.size() - 1; 
  }

  Slice* getSlice(uint32_t row) const {
    Assert (row < d_block.size()); 
    return d_block[row]; 
  }
  /** 
   * Propagate all the cut points in the Base to all the Slices. If one of the
   * splinters that needs to get cut has a pointer to a splinter in a different
   * block that splinter will also be split. 
   * 
   * @param queue other blocks that changed their base. 
   */
  void computeBlockBase(std::vector<RootId>& queue);

  void sliceBaseAt(Index i) {
    d_base.sliceAt(i); 
  }
  typedef std::vector<Slice*>::const_iterator const_iterator; 
  std::vector<Slice*>::const_iterator begin() {
    return d_block.begin(); 
  }
  std::vector<Slice*>::const_iterator end() {
    return d_block.end(); 
  }

  uint32_t getBitwidth() const {
    return d_bitwidth; 
  }
  Base& getBase() {
    return d_base; 
  }

  unsigned getSize() const {
    return d_block.size(); 
  }
  std::string debugPrint(); 
};

typedef __gnu_cxx::hash_map<TNode, bool, TNodeHashFunction> RootTermCache;

typedef __gnu_cxx::hash_map<TNode, RootId, TNodeHashFunction> NodeRootIdMap;
typedef std::vector<TNode> Roots; 

typedef __gnu_cxx::hash_map<TNode, SplinterId, TNodeHashFunction> NodeSplinterIdMap;
typedef std::vector<Splinter*> Splinters;

typedef std::vector<SliceBlock*> SliceBlocks;

class Slicer {
  std::vector<Node> d_simpleEqualities; /**< equalities of the form a[i0:j0] = b[i1:j1] */
  Roots d_roots;
  uint32_t d_numRoots; 
  NodeRootIdMap d_nodeRootMap;
  /* Indexed by Root Id */
  SliceBlocks d_rootBlocks;
  RootTermCache d_coreTermCache;
public:
  Slicer();
  void computeCoarsestBase();
  /** 
   * Takes an equality that is of the following form:
   *          a1 a2 ... an = b1 b2 ... bk
   * where ai, and bi are either variables or extracts over variables,
   * and consecutive extracts have been merged. 
   * 
   * @param node 
   */
  void processEquality(TNode node);
  bool isCoreTerm(TNode node); 
  static void splitEqualities(TNode node, std::vector<Node>& equalities);
private:
  void registerSimpleEquality(TNode node);

  TNode addSimpleTerm(TNode t);
  bool isRootTerm(TNode node);

  TNode getRoot(RootId id) {return d_roots[id]; }

  RootId getRootId(TNode node) {
    Assert (d_nodeRootMap.find(node) != d_nodeRootMap.end());
    return d_nodeRootMap[node]; 
  }

  RootId registerTerm(TNode node); 
  RootId makeRoot(TNode n);
  Slice* makeSlice(TNode node);

  bool debugCheckBase(); 
public:
  Slice* getSlice(const SplinterPointer& sp) {
    Assert (sp != Undefined); 
    SliceBlock* sb = d_rootBlocks[sp.term];
    return sb->getSlice(sp.row); 
  }
  
  Splinter* getSplinter(const SplinterPointer& sp) {
    Slice* slice = getSlice(sp);
    return slice->getSplinter(sp.index); 
  }

  SliceBlock* getSliceBlock(RootId id) {
    Assert (id < d_rootBlocks.size());
    return d_rootBlocks[id]; 
  }

  SliceBlock* getSliceBlock(const SplinterPointer& sp) {
    return getSliceBlock(sp.term); 
  }

  void getBaseDecomposition(TNode node, std::vector<Node>& decomp); 

}; /* Slicer class */

}/* CVC4::theory::bv namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */

#endif /* __CVC4__THEORY__BV__SLICER_BV_H */
