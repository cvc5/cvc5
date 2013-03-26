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
#include "theory/bv/theory_bv_utils.h"
#include "theory/rewriter.h"
#include "theory/bv/bv_subtheory_core.h"
using namespace CVC4;
using namespace CVC4::theory;
using namespace CVC4::theory::bv;
using namespace std; 


const TermId CVC4::theory::bv::UndefinedId = -1; 

/**
 * Base
 * 
 */
Base::Base(uint32_t size) 
  : d_size(size),
    d_repr(size/32 + (size % 32 == 0? 0 : 1), 0)
{
  Assert (d_size > 0); 
}

  
void Base::sliceAt(Index index) {
  if (index == d_size)
    return; 
  Assert(index < d_size); 
  Index vector_index = index / 32;
  Assert (vector_index < d_repr.size()); 
  Index int_index = index % 32;
  uint32_t bit_mask = utils::pow2(int_index); 
  d_repr[vector_index] = d_repr[vector_index] | bit_mask; 
}

void Base::undoSliceAt(Index index) {
  Index vector_index = index / 32;
  Assert (vector_index < d_size); 
  Index int_index = index % 32;
  uint32_t bit_mask = utils::pow2(int_index); 
  d_repr[vector_index] = d_repr[vector_index] ^ bit_mask; 
}

void Base::sliceWith(const Base& other) {
  Assert (d_size == other.d_size);
  for (unsigned i = 0; i < d_repr.size(); ++i) {
    d_repr[i] = d_repr[i] | other.d_repr[i]; 
  }
}

bool Base::isCutPoint (Index index) const {
  // there is an implicit cut point at the end and begining of the bv
  if (index == d_size || index == 0)
    return true;
    
  Index vector_index = index / 32;
  Assert (vector_index < d_size); 
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
  for (int i = d_size - 1; i >= 0; --i) {
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
 * ExtractTerm
 *
 */

std::string ExtractTerm::debugPrint() const {
  ostringstream os;
  os << "id" << id << "[" << high << ":" << low <<"] ";  
  return os.str(); 
}

/**
 * NormalForm
 *
 */

std::pair<TermId, Index> NormalForm::getTerm(Index index, const UnionFind& uf) const {
  Assert (index < base.getBitwidth()); 
  Index count = 0;
  for (unsigned i = 0; i < decomp.size(); ++i) {
    Index size = uf.getBitwidth(decomp[i]); 
    if ( count + size > index && index >= count) {
      return pair<TermId, Index>(decomp[i], count); 
    }
    count += size; 
  }
  Unreachable(); 
}



std::string NormalForm::debugPrint(const UnionFind& uf) const {
  ostringstream os;
  os << "NF " << base.debugPrint() << endl;
  os << "("; 
  for (int i = decomp.size() - 1; i>= 0; --i) {
    os << decomp[i] << "[" << uf.getBitwidth(decomp[i]) <<"]";
    os << (i != 0? ", " : "");  
  }
  os << ") \n"; 
  return os.str(); 
}
/**
 * UnionFind::EqualityNode
 * 
 */

std::string UnionFind::EqualityNode::debugPrint() const {
  ostringstream os;
  os << "Repr " << d_edge.repr << " ["<< d_bitwidth << "] ";
  os << "( " << d_ch1 <<", " << d_ch0 << ")" << endl; 
  return os.str(); 
}


/**
 * UnionFind
 * 
 */

TermId UnionFind::registerTopLevelTerm(Index bitwidth) {
  TermId id = mkEqualityNode(bitwidth);
  d_topLevelIds.insert(id);
  return id; 
}

TermId UnionFind::mkEqualityNode(Index bitwidth) {
  Assert (bitwidth > 0); 
  EqualityNode node(bitwidth);
  d_equalityNodes.push_back(node);
  
  ++(d_statistics.d_numNodes);
  
  TermId id = d_equalityNodes.size() - 1; 
  //  d_representatives.insert(id);
  ++(d_statistics.d_numRepresentatives); 
  Debug("bv-slicer-uf") << "UnionFind::addTerm " << id << " size " << bitwidth << endl;
  return id; 
}
/** 
 * Create an extract term making sure there are no nested extracts. 
 * 
 * @param id 
 * @param high 
 * @param low 
 * 
 * @return 
 */
ExtractTerm UnionFind::mkExtractTerm(TermId id, Index high, Index low) {
  if (d_topLevelIds.find(id) != d_topLevelIds.end()) {
    return ExtractTerm(id, high, low); 
  }
  Assert (isExtractTerm(id)); 
  ExtractTerm top = getExtractTerm(id);
  Assert (d_topLevelIds.find(top.id) != d_topLevelIds.end());
  
  Index top_low = top.low;
  Assert (top.high - top_low + 1 > high);
  high += top_low; 
  low += top_low;
  id = top.id; 
  return ExtractTerm(id, high, low); 
}

/** 
 * Associate the given extract term with the given id. 
 * 
 * @param id 
 * @param extract 
 */
void UnionFind::storeExtractTerm(TermId id, const ExtractTerm& extract) {
  if (d_extractToId.find(extract) != d_extractToId.end()) {
    Assert (d_extractToId[extract] == id); 
    return; 
  }
  Debug("bv-slicer") << "UnionFind::storeExtract " << extract.debugPrint() << " => id" << id << "\n";  
  d_idToExtract[id] = extract;
  d_extractToId[extract] = id; 
 }

TermId UnionFind::addEqualityNode(unsigned bitwidth, TermId id, Index high, Index low) {
  ExtractTerm extract(id, high, low);
  if (d_extractToId.find(extract) != d_extractToId.end()) {
    // if the extract already exists we don't need to make a new node
    TermId extract_id = d_extractToId[extract];
    Assert (extract_id < d_equalityNodes.size());
    return extract_id; 
  }
  // otherwise make an equality node for it and store the extract
  TermId node_id = mkEqualityNode(bitwidth);
  storeExtractTerm(node_id, extract);
  return node_id; 
}

/** 
 * At this point we assume the slicings of the two terms are properly aligned. 
 * 
 * @param t1 
 * @param t2 
 */
void UnionFind::unionTerms(TermId id1, TermId id2, TermId reason) {
  const ExtractTerm& t1 = getExtractTerm(id1);
  const ExtractTerm& t2 = getExtractTerm(id2);
  
  Debug("bv-slicer") << "UnionFind::unionTerms " << t1.debugPrint() << " and \n"
                     << "                      " << t2.debugPrint() << "\n"
                     << " with reason " << reason << endl;
  Assert (t1.getBitwidth() == t2.getBitwidth());
  
  NormalForm nf1(t1.getBitwidth());
  NormalForm nf2(t2.getBitwidth());
  
  getNormalForm(t1, nf1);
  getNormalForm(t2, nf2);

  Assert (nf1.decomp.size() == nf2.decomp.size());
  Assert (nf1.base == nf2.base);
  
  for (unsigned i = 0; i < nf1.decomp.size(); ++i) {
    merge (nf1.decomp[i], nf2.decomp[i], reason); 
  } 
}


/** 
 * Merge the two terms in the union find. Both t1 and t2
 * should be root terms. 
 * 
 * @param t1 
 * @param t2 
 */
void UnionFind::merge(TermId t1, TermId t2, TermId reason) {
  Debug("bv-slicer-uf") << "UnionFind::merge (" << t1 <<", " << t2 << ")" << endl;
  ++(d_statistics.d_numMerges);
  t1 = find(t1);
  t2 = find(t2); 

  if (t1 == t2)
    return;

  Assert (! hasChildren(t1) && ! hasChildren(t2));
  setRepr(t1, t2, reason);
  recordOperation(UnionFind::MERGE, t1); 
  //d_representatives.erase(t1);
  d_statistics.d_numRepresentatives += -1; 
}

TermId UnionFind::find(TermId id) {
  TermId repr = getRepr(id); 
  if (repr != UndefinedId) {
    TermId find_id =  find(repr);
    return find_id; 
  }
  return id; 
}

TermId UnionFind::findWithExplanation(TermId id, std::vector<ExplanationId>& explanation) {
  TermId repr = getRepr(id);

  if (repr != UndefinedId) {
    TermId reason = getReason(id);
    Assert (reason != UndefinedId); 
    explanation.push_back(reason);
  
    TermId find_id =  findWithExplanation(repr, explanation);
    return find_id; 
  }
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
  Debug("bv-slicer-uf") << "UnionFind::split " << id << " at " << i << endl;
  id = find(id); 
  Debug("bv-slicer-uf") << "   node: " << d_equalityNodes[id].debugPrint() << endl;

  if (i == 0 || i == getBitwidth(id)) {
    // nothing to do 
    return; 
  }

  Assert (i < getBitwidth(id));
  if (!hasChildren(id)) {
    // first time we split this term
    ExtractTerm bottom_extract = mkExtractTerm(id, i-1, 0);
    ExtractTerm top_extract = mkExtractTerm(id, getBitwidth(id) - 1, i);
    
    TermId bottom_id = extractHasId(bottom_extract)? getExtractId(bottom_extract) : mkEqualityNode(i); 
    TermId top_id = extractHasId(top_extract)? getExtractId(top_extract) : mkEqualityNode(getBitwidth(id) - i);
    storeExtractTerm(bottom_id, bottom_extract);
    storeExtractTerm(top_id, top_extract); 
    
    setChildren(id, top_id, bottom_id);
    recordOperation(UnionFind::SPLIT, id);
    
    if (d_slicer->termInEqualityEngine(id)) {
      d_slicer->enqueueSplit(id, i, top_id, bottom_id); 
    }
  } else {
    Index cut = getCutPoint(id); 
    if (i < cut )
      split(getChild(id, 0), i);
    else
      split(getChild(id, 1), i - cut); 
  }
  ++(d_statistics.d_numSplits);
}

// TermId UnionFind::getTopLevel(TermId id) const {
//   __gnu_cxx::hash_map<TermId, ExtractTerm, __gnu_cxx::hash<TermId> >::const_iterator it = d_idToExtract.find(id); 
//   if (it != d_idToExtract.end()) {
//     return (*it).second.id; 
//   }
//   return id; 
// }

void UnionFind::getNormalForm(const ExtractTerm& term, NormalForm& nf) {
  nf.clear(); 
  getDecomposition(term, nf.decomp);
  // update nf base
  Index count = 0; 
  for (unsigned i = 0; i < nf.decomp.size(); ++i) {
    count += getBitwidth(nf.decomp[i]);
    nf.base.sliceAt(count); 
  }
  Debug("bv-slicer-uf") << "UnionFind::getNormalFrom term: " << term.debugPrint() << endl;
  Debug("bv-slicer-uf") << "           nf: " << nf.debugPrint(*this) << endl; 
}

void UnionFind::getDecomposition(const ExtractTerm& term, Decomposition& decomp) {
  // making sure the term is aligned
  TermId id = find(term.id); 

  Assert (term.high < getBitwidth(id));
  // because we split the node, this must be the whole extract
  if (!hasChildren(id)) {
    Assert (term.high == getBitwidth(id) - 1 &&
            term.low == 0);
    decomp.push_back(id);
    return; 
  }
    
  Index cut = getCutPoint(id);
  
  if (term.low < cut && term.high < cut) {
    // the extract falls entirely on the low child
    ExtractTerm child_ex(getChild(id, 0), term.high, term.low); 
    getDecomposition(child_ex, decomp); 
  }
  else if (term.low >= cut && term.high >= cut){
    // the extract falls entirely on the high child
    ExtractTerm child_ex(getChild(id, 1), term.high - cut, term.low - cut);
    getDecomposition(child_ex, decomp); 
  }
  else {
    // the extract is split over the two children
    ExtractTerm low_child(getChild(id, 0), cut - 1, term.low);
    getDecomposition(low_child, decomp);
    ExtractTerm high_child(getChild(id, 1), term.high - cut, 0);
    getDecomposition(high_child, decomp); 
  }
}

void UnionFind::getNormalFormWithExplanation(const ExtractTerm& term, NormalForm& nf,
                                             std::vector<ExplanationId>& explanation) {
  nf.clear(); 
  getDecompositionWithExplanation(term, nf.decomp, explanation);
  // update nf base
  Index count = 0; 
  for (unsigned i = 0; i < nf.decomp.size(); ++i) {
    count += getBitwidth(nf.decomp[i]);
    nf.base.sliceAt(count); 
  }
  Debug("bv-slicer-uf") << "UnionFind::getNormalFrom term: " << term.debugPrint() << endl;
  Debug("bv-slicer-uf") << "           nf: " << nf.debugPrint(*this) << endl; 
}

void UnionFind::getDecompositionWithExplanation(const ExtractTerm& term, Decomposition& decomp,
                                                std::vector<ExplanationId>& explanation) {
  // making sure the term is aligned
  TermId id = findWithExplanation(term.id, explanation); 

  Assert (term.high < getBitwidth(id));
  // because we split the node, this must be the whole extract
  if (!hasChildren(id)) {
    Assert (term.high == getBitwidth(id) - 1 &&
            term.low == 0);
    decomp.push_back(id);
    return; 
  }
    
  Index cut = getCutPoint(id);
  
  if (term.low < cut && term.high < cut) {
    // the extract falls entirely on the low child
    ExtractTerm child_ex(getChild(id, 0), term.high, term.low); 
    getDecompositionWithExplanation(child_ex, decomp, explanation); 
  }
  else if (term.low >= cut && term.high >= cut){
    // the extract falls entirely on the high child
    ExtractTerm child_ex(getChild(id, 1), term.high - cut, term.low - cut);
    getDecompositionWithExplanation(child_ex, decomp, explanation); 
  }
  else {
    // the extract is split over the two children
    ExtractTerm low_child(getChild(id, 0), cut - 1, term.low);
    getDecompositionWithExplanation(low_child, decomp, explanation);
    ExtractTerm high_child(getChild(id, 1), term.high - cut, 0);
    getDecompositionWithExplanation(high_child, decomp, explanation); 
  }
}

/** 
 * May cause reslicings of the decompositions. Must not assume the decompositons
 * are the current normal form. 
 * 
 * @param d1 
 * @param d2 
 * @param common 
 */
void UnionFind::handleCommonSlice(const Decomposition& decomp1, const Decomposition& decomp2, TermId common) {
  Debug("bv-slicer") << "UnionFind::handleCommonSlice common = " << common << endl; 
  Index common_size = getBitwidth(common); 
  // find starting points of common slice
  Index start1 = 0;
  for (unsigned j = 0; j < decomp1.size(); ++j) {
    if (decomp1[j] == common)
      break;
    start1 += getBitwidth(decomp1[j]); 
  }

  Index start2 = 0; 
  for (unsigned j = 0; j < decomp2.size(); ++j) {
    if (decomp2[j] == common)
      break;
    start2 += getBitwidth(decomp2[j]); 
  }
  if (start1 > start2) {
    Index temp = start1;
    start1 = start2;
    start2 = temp; 
  }

  if (start2 - start1 < common_size) {
    Index overlap = start1 + common_size - start2;
    Assert (overlap > 0);
    Index diff = common_size - overlap;
    Assert (diff >= 0);
    Index granularity = utils::gcd(diff, overlap);
    // split the common part 
    for (unsigned i = 0; i < common_size; i+= granularity) {
      split(common, i); 
    }
  }

}

void UnionFind::alignSlicings(TermId id1, TermId id2) {
  const ExtractTerm& term1 = getExtractTerm(id1);
  const ExtractTerm& term2 = getExtractTerm(id2);
  
  Debug("bv-slicer") << "UnionFind::alignSlicings " << term1.debugPrint() << endl;
  Debug("bv-slicer") << "                         " << term2.debugPrint() << endl;
  NormalForm nf1(term1.getBitwidth());
  NormalForm nf2(term2.getBitwidth());
  
  getNormalForm(term1, nf1);
  getNormalForm(term2, nf2);

  Assert (nf1.base.getBitwidth() == nf2.base.getBitwidth());
  
  // first check if the two have any common slices 
  std::vector<TermId> intersection; 
  utils::intersect(nf1.decomp, nf2.decomp, intersection); 
  for (unsigned i = 0; i < intersection.size(); ++i) {
    // handle common slice may change the normal form 
    handleCommonSlice(nf1.decomp, nf2.decomp, intersection[i]); 
  }
  // propagate cuts to a fixpoint 
  bool changed;
  Base cuts(term1.getBitwidth()); 
  do {
    changed = false; 
    // we need to update the normal form which may have changed 
    getNormalForm(term1, nf1);
    getNormalForm(term2, nf2); 

    // align the cuts points of the two slicings
    // FIXME: this can be done more efficiently
    cuts.sliceWith(nf1.base);
    cuts.sliceWith(nf2.base); 

    for (unsigned i = 0; i < cuts.getBitwidth(); ++i) {
      if (cuts.isCutPoint(i)) {
        if (!nf1.base.isCutPoint(i)) {
          pair<TermId, Index> pair1 = nf1.getTerm(i, *this);
          split(pair1.first, i - pair1.second);
          changed = true; 
        }
        if (!nf2.base.isCutPoint(i)) {
          pair<TermId, Index> pair2 = nf2.getTerm(i, *this);
          split(pair2.first, i - pair2.second);
          changed = true; 
        }
      }
    }
  } while (changed); 
}


/** 
 * Given an extract term a[i:j] makes sure a is sliced
 * at indices i and j. 
 * 
 * @param term 
 */
void UnionFind::ensureSlicing(TermId t) {
  ExtractTerm term = getExtractTerm(t); 
  //Debug("bv-slicer") << "Slicer::ensureSlicing " << term.debugPrint() << endl;
  TermId id = term.id; 
  split(id, term.high + 1);
  split(id, term.low);
}

void UnionFind::backtrack() {
  int size = d_undoStack.size(); 
  for (int i = size; i > (int)d_undoStackIndex.get(); --i) {
    Assert (!d_undoStack.empty()); 
    Operation op = d_undoStack.back(); 
    d_undoStack.pop_back();
    if (op.op == UnionFind::MERGE) {
      undoMerge(op.id); 
    } else {
      Assert (op.op == UnionFind::SPLIT);
      undoSplit(op.id); 
    }
  }
}

void UnionFind::undoMerge(TermId id) {
  Assert (getRepr(id) != UndefinedId);
  setRepr(id, UndefinedId, UndefinedId); 
}

void UnionFind::undoSplit(TermId id) {
  Assert (hasChildren(id));
  setChildren(id, UndefinedId, UndefinedId); 
}

void UnionFind::recordOperation(OperationKind op, TermId term) {
  d_undoStackIndex.set(d_undoStackIndex.get() + 1);
  d_undoStack.push_back(Operation(op, term));
  Assert (d_undoStack.size() == d_undoStackIndex); 
}

void UnionFind::getBase(TermId id, Base& base, Index offset) {
  id = find(id); 
  if (!hasChildren(id))
    return;
  TermId id1 = find(getChild(id, 1));
  TermId id0 = find(getChild(id, 0));
  Index cut = getCutPoint(id);
  base.sliceAt(cut + offset);
  getBase(id1, base, cut + offset);
  getBase(id0, base, offset); 
}

/// getter methods for the internal nodes
TermId UnionFind::getRepr(TermId id)  const {
  Assert (id < d_equalityNodes.size());
  return d_equalityNodes[id].getRepr(); 
}
ExplanationId UnionFind::getReason(TermId id) const {
  Assert (id < d_equalityNodes.size());
  return d_equalityNodes[id].getReason(); 
}
TermId UnionFind::getChild(TermId id, Index i) const {
  Assert (id < d_equalityNodes.size());
  return d_equalityNodes[id].getChild(i); 
}
Index UnionFind::getCutPoint(TermId id) const {
  return getBitwidth(getChild(id, 0)); 
}
bool UnionFind::hasChildren(TermId id) const {
  Assert (id < d_equalityNodes.size());
  return d_equalityNodes[id].hasChildren(); 
}
  
/// setter methods for the internal nodes
void UnionFind::setRepr(TermId id, TermId new_repr, ExplanationId reason) {
  Assert (id < d_equalityNodes.size());
  d_equalityNodes[id].setRepr(new_repr, reason); 
}
void UnionFind::setChildren(TermId id, TermId ch1, TermId ch0) {
  Assert ((ch1 == UndefinedId && ch0 == UndefinedId) ||
          (id < d_equalityNodes.size() && getBitwidth(id) == getBitwidth(ch1) + getBitwidth(ch0)));
  d_equalityNodes[id].setChildren(ch1, ch0); 
}


/**
 * Slicer
 * 
 */

TermId Slicer::registerTerm(TNode node) {
  if (node.getKind() == kind::BITVECTOR_EXTRACT) {
    TNode n = node[0];
    TermId top_id = registerTopLevelTerm(n);
    Index high = utils::getExtractHigh(node);
    Index low = utils::getExtractLow(node);
    TermId id = d_unionFind.addEqualityNode(utils::getSize(node), top_id, high, low); 
    return id; 
  }
  TermId id = registerTopLevelTerm(node);
  return id; 
}

TermId Slicer::registerTopLevelTerm(TNode node) {
  Assert (node.getKind() != kind::BITVECTOR_EXTRACT ||
          node.getKind() != kind::BITVECTOR_CONCAT);
  
  if (d_nodeToId.find(node) == d_nodeToId.end()) {
    TermId id = d_unionFind.registerTopLevelTerm(utils::getSize(node)); 
    d_idToNode[id] = node; 
    d_nodeToId[node] = id;
    Debug("bv-slicer") << "Slicer::registerTopLevelTerm " << node << " => id" << id << endl;
    return id; 
  }
  return d_nodeToId[node]; 
}

void Slicer::processEquality(TNode eq) {
  Debug("bv-slicer") << "Slicer::processEquality: " << eq << endl;

  registerEquality(eq); 
  Assert (eq.getKind() == kind::EQUAL);
  TNode a = eq[0];
  TNode b = eq[1];
  TermId a_id = registerTerm(a);
  TermId b_id = registerTerm(b);
  
  d_unionFind.ensureSlicing(a_id);
  d_unionFind.ensureSlicing(b_id);
  
  d_unionFind.alignSlicings(a_id, b_id);

  // Debug("bv-slicer") << "Base of " << a_ex.id <<" " << d_unionFind.debugPrint(a_ex.id) << endl;
  // Debug("bv-slicer") << "Base of " << b_ex.id <<" " << d_unionFind.debugPrint(b_ex.id) << endl;
  // Debug("bv-slicer") << "Slicer::processEquality done. " << endl;
}

void Slicer::assertEquality(TNode eq) {
  Assert (eq.getKind() == kind::EQUAL);
  TermId a = registerTerm(eq[0]);
  TermId b = registerTerm(eq[1]);
  ExplanationId reason = getExplanationId(eq); 
  d_unionFind.unionTerms(a, b, reason); 
}


void Slicer::registerEquality(TNode eq) {
  if (d_explanationToId.find(eq) == d_explanationToId.end()) {
    ExplanationId id = d_explanations.size(); 
    d_explanations.push_back(eq);
    d_explanationToId[eq] = id;
    Debug("bv-slicer-explanation") << "Slicer::registerEquality " << eq << " => id"<< id << "\n";  
  }
}

void Slicer::getBaseDecomposition(TNode node, std::vector<Node>& decomp, std::vector<TNode>& explanation) {
  Debug("bv-slicer") << "Slicer::getBaseDecomposition " << node << endl;
  
  Index high = utils::getSize(node) - 1;
  Index low = 0;
  TNode top = node; 
  if (node.getKind() == kind::BITVECTOR_EXTRACT) {
    high = utils::getExtractHigh(node);
    low = utils::getExtractLow(node);
    top = node[0]; 
  }
  
  Assert (d_nodeToId.find(top) != d_nodeToId.end()); 
  TermId id = d_nodeToId[top];
  NormalForm nf(high-low+1);
  std::vector<ExplanationId> explanation_ids; 
  d_unionFind.getNormalFormWithExplanation(ExtractTerm(id, high, low), nf, explanation_ids);

  for (unsigned i = 0; i < explanation_ids.size(); ++i) {
    Assert (hasExplanation(explanation_ids[i])); 
    TNode exp = getExplanation(explanation_ids[i]);
    explanation.push_back(exp); 
  }
  
  for (int i = nf.decomp.size() - 1; i>=0 ; --i) {
    Node current = getNode(nf.decomp[i]); 
    decomp.push_back(current); 
  }
  if (Debug.isOn("bv-slicer-explanation")) {
    Debug("bv-slicer-explanation") << "Slicer::getBaseDecomposition for " << node << "\n"
                                   << "as ";
    for (unsigned i = 0; i < decomp.size(); ++i) {
      Debug("bv-slicer-explanation") << decomp[i] <<" " ; 
    }
    Debug("bv-slicer-explanation") << "\n Explanation : \n";
    for (unsigned i = 0; i < explanation.size(); ++i) {
      Debug("bv-slicer-explanation") << "   " << explanation[i] << "\n"; 
    }
    
  }

}

bool Slicer::isCoreTerm(TNode node) {
  if (d_coreTermCache.find(node) == d_coreTermCache.end()) {
    Kind kind = node.getKind(); 
    if (kind != kind::BITVECTOR_EXTRACT &&
        kind != kind::BITVECTOR_CONCAT &&
        kind != kind::EQUAL &&
        kind != kind::STORE &&
        kind != kind::SELECT &&
        kind != kind::NOT &&
        node.getMetaKind() != kind::metakind::VARIABLE &&
        kind != kind::CONST_BITVECTOR) {
      d_coreTermCache[node] = false;
      return false; 
    } else {
      // we need to recursively check whether the term is a root term or not
      bool isCore = true;
      for (unsigned i = 0; i < node.getNumChildren(); ++i) {
        isCore = isCore && isCoreTerm(node[i]); 
      }
      d_coreTermCache[node] = isCore;
      return isCore; 
    }
  }
  return d_coreTermCache[node]; 
}
unsigned Slicer::d_numAddedEqualities = 0; 

void Slicer::splitEqualities(TNode node, std::vector<Node>& equalities) {
  Assert (node.getKind() == kind::EQUAL);
  TNode t1 = node[0];
  TNode t2 = node[1];

  uint32_t width = utils::getSize(t1); 
  
  Base base1(width); 
  if (t1.getKind() == kind::BITVECTOR_CONCAT) {
    int size = 0;
    // no need to count the last child since the end cut point is implicit 
    for (int i = t1.getNumChildren() - 1; i >= 1 ; --i) {
      size = size + utils::getSize(t1[i]);
      base1.sliceAt(size); 
    }
  }

  Base base2(width); 
  if (t2.getKind() == kind::BITVECTOR_CONCAT) {
    unsigned size = 0; 
    for (int i = t2.getNumChildren() - 1; i >= 1; --i) {
      size = size + utils::getSize(t2[i]);
      base2.sliceAt(size); 
    }
  }

  base1.sliceWith(base2); 
  if (!base1.isEmpty()) {
    // we split the equalities according to the base
    int last = 0; 
    for (unsigned i = 1; i <= utils::getSize(t1); ++i) {
      if (base1.isCutPoint(i)) {
        Node extract1 = utils::mkExtract(t1, i-1, last);
        Node extract2 = utils::mkExtract(t2, i-1, last);
        last = i;
        Assert (utils::getSize(extract1) == utils::getSize(extract2)); 
        equalities.push_back(utils::mkNode(kind::EQUAL, extract1, extract2)); 
      }
    }
  } else {
    // just return same equality
    equalities.push_back(node);
  }
  d_numAddedEqualities += equalities.size() - 1; 
}


ExtractTerm UnionFind::getExtractTerm(TermId id) const {
  if (d_topLevelIds.find(id) != d_topLevelIds.end()) {
    // if it's a top level term so we don't have an extract stored for it
    return ExtractTerm(id, getBitwidth(id) - 1, 0); 
  }
  Assert (isExtractTerm(id));
  
  return (d_idToExtract.find(id))->second; 
}

bool UnionFind::isExtractTerm(TermId id) const {
  return d_idToExtract.find(id) != d_idToExtract.end();
}

bool Slicer::isTopLevelNode(TermId id) const {
  return d_idToNode.find(id) != d_idToNode.end(); 
}

Node Slicer::getNode(TermId id) const {
  if (isTopLevelNode(id)) {
    return d_idToNode.find(id)->second; 
  }
  Assert (d_unionFind.isExtractTerm(id)); 
  const ExtractTerm& extract = d_unionFind.getExtractTerm(id);
  Assert (isTopLevelNode(extract.id)); 
  TNode node = d_idToNode.find(extract.id)->second;
  if (extract.high == utils::getSize(node) -1 && extract.low == 0) {
    return node; 
  }
  Node ex = utils::mkExtract(node, extract.high, extract.low);
  return ex; 
}

bool Slicer::termInEqualityEngine(TermId id) {
  Node node = getNode(id); 
  return d_coreSolver->hasTerm(node); 
}

void Slicer::enqueueSplit(TermId id, Index i, TermId top_id, TermId bottom_id) {
  Node node = getNode(id);
  Node bottom = Rewriter::rewrite(utils::mkExtract(node, i -1 , 0));
  Node top = Rewriter::rewrite(utils::mkExtract(node, utils::getSize(node) - 1, i));
  // must add terms to equality engine so we get notified when they get split more
  d_coreSolver->addTermToEqualityEngine(bottom);
  d_coreSolver->addTermToEqualityEngine(top);

  Node eq = utils::mkNode(kind::EQUAL, node, utils::mkConcat(top, bottom));
  d_newSplits.push_back(eq);
  Debug("bv-slicer") << "Slicer::enqueueSplit " << eq << endl;
  Debug("bv-slicer") << "                     " << id << "=" << top_id << " " << bottom_id << endl; 
}

void Slicer::getNewSplits(std::vector<Node>& splits) {
  for (unsigned i = d_newSplitsIndex; i < d_newSplits.size(); ++i) {
    splits.push_back(d_newSplits[i]);
  }
  d_newSplitsIndex = d_newSplits.size(); 
}

bool Slicer::hasExplanation(ExplanationId id) const {
  return id < d_explanations.size(); 
}

TNode Slicer::getExplanation(ExplanationId id) const {
  Assert(hasExplanation(id));
  return d_explanations[id]; 
}

ExplanationId Slicer::getExplanationId(TNode reason) const {
  Assert (d_explanationToId.find(reason) != d_explanationToId.end());
  return d_explanationToId.find(reason)->second; 
}

std::string UnionFind::debugPrint(TermId id) {
  ostringstream os; 
  if (hasChildren(id)) {
    TermId id1 = find(getChild(id, 1));
    TermId id0 = find(getChild(id, 0));
    os << debugPrint(id1);
    os << debugPrint(id0); 
  } else {
    if (getRepr(id) == UndefinedId) {
      os <<"id"<< id <<"[" << getBitwidth(id) <<"] "; 
    } else {
      os << debugPrint(find(id));
    }
  }
  return os.str(); 
}

UnionFind::Statistics::Statistics():
  d_numNodes("theory::bv::slicer::NumberOfNodes", 0),
  d_numRepresentatives("theory::bv::slicer::NumberOfRepresentatives", 0),
  d_numSplits("theory::bv::slicer::NumberOfSplits", 0),
  d_numMerges("theory::bv::slicer::NumberOfMerges", 0),
  d_avgFindDepth("theory::bv::slicer::AverageFindDepth"),
  d_numAddedEqualities("theory::bv::slicer::NumberOfEqualitiesAdded", Slicer::d_numAddedEqualities)
{
  StatisticsRegistry::registerStat(&d_numRepresentatives);
  StatisticsRegistry::registerStat(&d_numSplits);
  StatisticsRegistry::registerStat(&d_numMerges);
  StatisticsRegistry::registerStat(&d_avgFindDepth);
  StatisticsRegistry::registerStat(&d_numAddedEqualities);
}

UnionFind::Statistics::~Statistics() {
  StatisticsRegistry::unregisterStat(&d_numRepresentatives);
  StatisticsRegistry::unregisterStat(&d_numSplits);
  StatisticsRegistry::unregisterStat(&d_numMerges);
  StatisticsRegistry::unregisterStat(&d_avgFindDepth);
  StatisticsRegistry::unregisterStat(&d_numAddedEqualities);
}
