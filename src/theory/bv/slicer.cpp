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

#include "theory/bv/slicer.h"
#include "util/utility.h"
#include "theory/bv/theory_bv_utils.h"
#include "theory/rewriter.h"

using namespace CVC4;
using namespace CVC4::theory;
using namespace CVC4::theory::bv;
using namespace std; 

/**
 * Base
 * 
 */
Base::Base(uint32_t size) 
  : d_size(size),
    d_repr((size-1)/32 + ((size-1) % 32 == 0? 0 : 1), 0)
{
  Assert (d_size > 0); 
}

  
void Base::sliceAt(Index index) {
  Index vector_index = index / 32;
  Assert (vector_index < d_size - 1); 
  Index int_index = index % 32;
  uint32_t bit_mask = utils::pow2(int_index); 
  d_repr[vector_index] = d_repr[vector_index] | bit_mask; 
}

void Base::sliceWith(const Base& other) {
  Assert (d_size == other.d_size);
  for (unsigned i = 0; i < d_repr.size(); ++i) {
    d_repr[i] = d_repr[i] | other.d_repr[i]; 
  }
}

bool Base::isCutPoint (Index index) const {
  // there is an implicit cut point at the end of the bv
  if (index == d_size - 1)
    return true;
    
  Index vector_index = index / 32;
  Assert (vector_index < d_size - 1); 
  Index int_index = index % 32;
  uint32_t bit_mask = utils::pow2(int_index); 

  return (bit_mask & d_repr[vector_index]) != 0; 
}

void Base::diffCutPoints(const Base& other, Base& res) const {
  Assert (d_size == other.d_size && res.d_size == d_size);
  for (unsigned i = 0; i < d_repr.size(); ++i) {
    Assert (res.d_repr[i] == 0); 
    res.d_repr[i] = d_repr[i] ^ other.d_repr[i]; 
  }
}

bool Base::isEmpty() const {
  for (unsigned i = 0; i< d_repr.size(); ++i) {
    if (d_repr[i] != 0)
      return false;
  }
  return true;
}

std::string Base::debugPrint() const {
  std::ostringstream os;
  os << "[";
  bool first = true; 
  for (unsigned i = 0; i < d_size - 1; ++i) {
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
 
 
/**
 * UnionFind
 * 
 */
TermId UnionFind::addTerm(Index bitwidth) {
  Node node(bitwidth);
  d_nodes.push_back(node);
  TermId id = d_nodes.size() - 1; 
  d_representatives.insert(id);
  d_topLevelTerms.insert(id); 
}

void UnionFind::merge(TermId t1, TermId t2) {
  
}
TermId UnionFind::find(TermId id) {
  Node node = getNode(id); 
  if (node.getRepr() != -1)
    return find(node.getRepr());
  return id; 
}
/** 
 * Splits the representative of the term between i-1 and i
 * 
 * @param id the id of the term
 * @param i the index we are splitting at
 * 
 * @return 
 */
void UnionFind::split(TermId id, Index i) {
  id = find(id); 
  Node node = getNode(id); 
  Assert (i < node.getBitwidth());

  if (i == 0 || i == node.getBitwidth()) {
    // nothing to do 
    return;
  }

  if (!node.hasChildren()) {
    // first time we split this term 
    TermId bottom_id = addTerm(i);
    TermId top_id = addTerm(node.getBitwidth() - i);
    node.addChildren(top_id, bottom_id);

  } else {
    Index cut = node.getCutPoint(); 
    if (i < cut )
      split(child1, i);
    else
      split(node.getChild(1), i - cut); 
  }
}

void UnionFind::getNormalForm(ExtractTerm term, NormalForm& nf) {
  TermId id = find(term.id);
  getDecomposition(term, nf.decomp);
  // update nf base
  Index count = 0; 
  for (unsigned i = 0; i < nf.decomp.size(); ++i) {
    count += getBitwidth(nf.decomp[i]);
    nf.base.sliceAt(count); 
  }
}

void UnionFind::getDecomposition(ExtractTerm term, Decomposition& decomp) {
  // making sure the term is aligned
  TermId id = find(term.id); 

  Node node = getNode(id);
  Assert (term.high < node.getBitwidth());
  // because we split the node, this must be the whole extract
  if (!node.hasChildren()) {
    Assert (term.high == node.getBitwidth() - 1 &&
            term.low == 0);
    decomp.push_back(id); 
  }
    
  Index cut = node.getCutPoint();
  
  if (low < cut && high < cut) {
    // the extract falls entirely on the low child
    ExtractTerm child_ex(node.getChild(0), high, low); 
    getDecomposition(child_ex, decomp); 
  }
  else if (low >= cut && high >= cut){
    // the extract falls entirely on the high child
    ExtractTerm child_ex(node.getChild(1), high - cut, low - cut);
    getDecomposition(child_ex, decomp); 
  }
  else {
    // the extract is split over the two children
    ExtractTerm low_child(node.getChild(0), cut - 1, low);
    getDecomposition(low_child, decomp);
    ExtractTerm high_child(node.getChild(1), high, cut);
    getDecomposition(high_child, decomp); 
  }
}

void UnionFind::alignSlicings(NormalForm& nf1, NormalForm& nf2) {
  Assert (nf1.base.getBitwidth() == nf2.base.getBitwidth());
  // check if the two have
  std::vector<TermId> intersection; 
  intersection(nf1.decomp, nf2.decomp, intersection); 
  for (unsigned i = 0; i < intersection.size(); ++i) {
    TermId overlap = intersection[i];
    Index start1 = 0;
    Decomposition& decomp1 = nf1.decomp; 
    for (unsigned j = 0; j < decomp1.size(); ++j) {
      if (decomp1[j] == overlap)
        break;
      start1 += getSize(decomp1[j]); 
    }
  }
  
  Base new_cuts1 = nf1.base.diffCutPoints(nf2.base);
  Base new_cuts2 = nf2.base.diffCutPoints(nf1.base); 
  for (unsigned i = 0; i < new_cuts.base.getBitwidth(); ++i) {
    if (new_cuts1.isCutPoint(i)) {
      
    }
  }
  
}

void UnionFind::ensureSlicing(ExtractTerm& term) {
  TermId id = find(term.id);
  split(id, term.high);
  split(id, term.low);

  
}

/**
 * Slicer
 * 
 */



void Slicer::registerTerm(TNode node) {
  Index low = 0, high = utils::getSize(node); 
  TNode n = node; 
  if (node.getKind() == kind::BITVECTOR_EXTRACT) {
    TNode n = node[0];
    high = utils::getExtractHigh(node);
    low = utils::getExtractLow(node); 
  }
  if (d_nodeToId.find(n) == d_nodeToId.end()) {
    id = d_uf.addTerm(utils::getSize(n)); 
    d_nodeToId[n] = id;
    d_idToNode[id] = n; 
  }
  TermId id = d_nodeToId[n];

  return ExtractTerm(id, high, low); 
}

void Slicer::processSimpleEquality(TNode eq) {
  Assert (eq.getKind() == kind::EQUAL);
  TNode a = eq[0];
  TNode b = eq[1];
  ExtractTerm a_ex= registerTerm(a);
  ExtractTerm b_ex= registerTerm(b);
  
  NormalForm a_nf, b_nf;
  d_uf.ensureSlicing(a_ex);
  d_uf.ensureSlicing(b_ex);
  
  d_uf.getNormalForm(a_ex, a_nf);
  d_uf.getNormalForm(b_ex, b_nf);

  d_uf.alignSlicings(a_nf, b_nf); 
}

void Slicer::getBaseDecomposition(TNode node, std::vector<Node>& decomp) const {
}


