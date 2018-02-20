/*********************                                                        */
/*! \file slicer.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Liana Hadarean, Aina Niemetz, Tim King
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2018 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Bitvector theory.
 **
 ** Bitvector theory.
 **/
#include "theory/bv/slicer.h"

#include "options/bv_options.h"
#include "smt/smt_statistics_registry.h"
#include "theory/bv/theory_bv_utils.h"
#include "theory/rewriter.h"

using namespace std; 


namespace CVC4 {
namespace theory {
namespace bv {

const TermId UndefinedId = -1;

namespace {

void intersect(const std::vector<TermId>& v1,
               const std::vector<TermId>& v2,
               std::vector<TermId>& intersection)
{
  for (const TermId id1 : v1)
  {
    for (const TermId id2 : v2)
    {
      if (id2 == id1)
      {
        intersection.push_back(id1);
        break;
      }
    }
  }
}

}  // namespace

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

void Base::sliceAt(Index index)
{
  Index vector_index = index / 32;
  if (vector_index == d_repr.size())
    return;

  Index int_index = index % 32;
  uint32_t bit_mask = 1u << int_index;
  d_repr[vector_index] = d_repr[vector_index] | bit_mask;
}

void Base::sliceWith(const Base& other) {
  Assert (d_size == other.d_size);
  for (unsigned i = 0; i < d_repr.size(); ++i) {
    d_repr[i] = d_repr[i] | other.d_repr[i]; 
  }
}

bool Base::isCutPoint (Index index) const
{
  // there is an implicit cut point at the end and begining of the bv
  if (index == d_size || index == 0)
    return true;

  Index vector_index = index / 32;
  Assert (vector_index < d_size);
  Index int_index = index % 32;
  uint32_t bit_mask = 1u << int_index;

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
 * UnionFind::Node
 * 
 */

std::string UnionFind::Node::debugPrint() const {
  ostringstream os;
  os << "Repr " << d_repr << " ["<< d_bitwidth << "] ";
  os << "( " << d_ch1 <<", " << d_ch0 << ")" << endl; 
  return os.str(); 
}


/**
 * UnionFind
 * 
 */
TermId UnionFind::addTerm(Index bitwidth) {
  Node node(bitwidth);
  d_nodes.push_back(node);
  ++(d_statistics.d_numNodes);
  
  TermId id = d_nodes.size() - 1; 
  d_representatives.insert(id);
  ++(d_statistics.d_numRepresentatives); 

  Debug("bv-slicer-uf") << "UnionFind::addTerm " << id << " size " << bitwidth << endl;
  return id; 
}
/** 
 * At this point we assume the slicings of the two terms are properly aligned. 
 * 
 * @param t1 
 * @param t2 
 */
void UnionFind::unionTerms(const ExtractTerm& t1, const ExtractTerm& t2) {
  Debug("bv-slicer") << "UnionFind::unionTerms " << t1.debugPrint() << " and \n"
                     << "                      " << t2.debugPrint() << endl;
  Assert (t1.getBitwidth() == t2.getBitwidth());
  
  NormalForm nf1(t1.getBitwidth());
  NormalForm nf2(t2.getBitwidth());
  
  getNormalForm(t1, nf1);
  getNormalForm(t2, nf2);

  Assert (nf1.decomp.size() == nf2.decomp.size());
  Assert (nf1.base == nf2.base);
  
  for (unsigned i = 0; i < nf1.decomp.size(); ++i) {
    merge (nf1.decomp[i], nf2.decomp[i]); 
  } 
}

/** 
 * Merge the two terms in the union find. Both t1 and t2
 * should be root terms. 
 * 
 * @param t1 
 * @param t2 
 */
void UnionFind::merge(TermId t1, TermId t2) {
  Debug("bv-slicer-uf") << "UnionFind::merge (" << t1 <<", " << t2 << ")" << endl;
  ++(d_statistics.d_numMerges);
  t1 = find(t1);
  t2 = find(t2); 

  if (t1 == t2)
    return;

  Assert (! hasChildren(t1) && ! hasChildren(t2));
  setRepr(t1, t2); 
  d_representatives.erase(t1);
  d_statistics.d_numRepresentatives += -1; 
}

TermId UnionFind::find(TermId id) {
  TermId repr = getRepr(id); 
  if (repr != UndefinedId) {
    TermId find_id =  find(repr);
    setRepr(id, find_id);
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
  Debug("bv-slicer-uf") << "   node: " << d_nodes[id].debugPrint() << endl;

  if (i == 0 || i == getBitwidth(id)) {
    // nothing to do 
    return;
  }
  Assert (i < getBitwidth(id));
  if (!hasChildren(id)) {
    // first time we split this term 
    TermId bottom_id = addTerm(i);
    TermId top_id = addTerm(getBitwidth(id) - i);
    setChildren(id, top_id, bottom_id);

  } else {
    Index cut = getCutPoint(id); 
    if (i < cut )
      split(getChild(id, 0), i);
    else
      split(getChild(id, 1), i - cut); 
  }
  ++(d_statistics.d_numSplits);
}

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

/* Compute the greatest common divisor of two indices.  */
static Index gcd(Index a, Index b)
{
  while (b != 0)
  {
    Index t = b;
    b = a % t;
    a = t;
  }
  return a;
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
    Index granularity = gcd(diff, overlap);
    // split the common part 
    for (unsigned i = 0; i < common_size; i+= granularity) {
      split(common, i); 
    }
  }

}

void UnionFind::alignSlicings(const ExtractTerm& term1, const ExtractTerm& term2) {
  Debug("bv-slicer") << "UnionFind::alignSlicings " << term1.debugPrint() << endl;
  Debug("bv-slicer") << "                         " << term2.debugPrint() << endl;
  NormalForm nf1(term1.getBitwidth());
  NormalForm nf2(term2.getBitwidth());

  getNormalForm(term1, nf1);
  getNormalForm(term2, nf2);

  Assert (nf1.base.getBitwidth() == nf2.base.getBitwidth());

  // first check if the two have any common slices
  std::vector<TermId> intersection;
  intersect(nf1.decomp, nf2.decomp, intersection);
  for (TermId id : intersection)
  {
    /* handleCommonSlice() may change the normal form */
    handleCommonSlice(nf1.decomp, nf2.decomp, id);
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
void UnionFind::ensureSlicing(const ExtractTerm& term) {
  //Debug("bv-slicer") << "Slicer::ensureSlicing " << term.debugPrint() << endl;
  TermId id = find(term.id);
  split(id, term.high + 1);
  split(id, term.low);
}

/**
 * Slicer
 * 
 */

ExtractTerm Slicer::registerTerm(TNode node) {
  Index low = 0, high = utils::getSize(node) - 1; 
  TNode n = node; 
  if (node.getKind() == kind::BITVECTOR_EXTRACT) {
    n = node[0];
    high = utils::getExtractHigh(node);
    low = utils::getExtractLow(node); 
  }
  if (d_nodeToId.find(n) == d_nodeToId.end()) {
    TermId id = d_unionFind.addTerm(utils::getSize(n)); 
    d_nodeToId[n] = id;
    d_idToNode[id] = n; 
  }
  TermId id = d_nodeToId[n];
  ExtractTerm res(id, high, low); 
  Debug("bv-slicer") << "Slicer::registerTerm " << node << " => " << res.debugPrint() << endl;
  return res; 
}

void Slicer::processEquality(TNode eq) {
  Debug("bv-slicer") << "Slicer::processEquality: " << eq << endl;
  
  Assert (eq.getKind() == kind::EQUAL);
  TNode a = eq[0];
  TNode b = eq[1];
  ExtractTerm a_ex= registerTerm(a);
  ExtractTerm b_ex= registerTerm(b);
  
  d_unionFind.ensureSlicing(a_ex);
  d_unionFind.ensureSlicing(b_ex);
  
  d_unionFind.alignSlicings(a_ex, b_ex);
  d_unionFind.unionTerms(a_ex, b_ex);
  Debug("bv-slicer") << "Base of " << a_ex.id <<" " << d_unionFind.debugPrint(a_ex.id) << endl;
  Debug("bv-slicer") << "Base of " << b_ex.id <<" " << d_unionFind.debugPrint(b_ex.id) << endl;
  Debug("bv-slicer") << "Slicer::processEquality done. " << endl;
}

void Slicer::getBaseDecomposition(TNode node, std::vector<Node>& decomp) {
  Debug("bv-slicer") << "Slicer::getBaseDecomposition " << node << endl;
  
  Index high = utils::getSize(node) - 1;
  Index low = 0;
  TNode top = node; 
  if (node.getKind() == kind::BITVECTOR_EXTRACT) {
    high = utils::getExtractHigh(node);
    low = utils::getExtractLow(node);
    top = node[0]; 
  }
  AlwaysAssert (d_nodeToId.find(top) != d_nodeToId.end()); 
  TermId id = d_nodeToId[top];
  NormalForm nf(high-low+1); 
  d_unionFind.getNormalForm(ExtractTerm(id, high, low), nf);
  
  // construct actual extract nodes
  unsigned size = utils::getSize(node); 
  Index current_low = size;
  Index current_high = size; 
  for (int i = nf.decomp.size() - 1; i >= 0; --i) {
    Index current_size = d_unionFind.getBitwidth(nf.decomp[i]); 
    current_low -= current_size; 
    Node current = Rewriter::rewrite(utils::mkExtract(node, current_high - 1, current_low));
    current_high = current_low;
    decomp.push_back(current); 
  }

  Debug("bv-slicer") << "as [";
  for (unsigned i = 0; i < decomp.size(); ++i) {
    Debug("bv-slicer") << decomp[i] <<" "; 
  }
  Debug("bv-slicer") << "]" << endl;

}

bool Slicer::isCoreTerm(TNode node) {
  if (d_coreTermCache.find(node) == d_coreTermCache.end()) {
    Kind kind = node.getKind();
    bool not_core;
    if (options::bitvectorEqualitySlicer() != BITVECTOR_SLICER_OFF) {
      not_core = (kind != kind::BITVECTOR_EXTRACT && kind != kind::BITVECTOR_CONCAT); 
    } else {
      not_core = true; 
    }
    if (not_core &&
        kind != kind::EQUAL &&
        kind != kind::NOT &&
        kind != kind::STORE &&
        kind != kind::SELECT &&
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

void Slicer::splitEqualities(TNode node, std::vector<Node>& equalities)
{
  Assert(node.getKind() == kind::EQUAL);
  NodeManager* nm = NodeManager::currentNM();
  TNode t1 = node[0];
  TNode t2 = node[1];

  uint32_t width = utils::getSize(t1);

  Base base1(width);
  if (t1.getKind() == kind::BITVECTOR_CONCAT)
  {
    int size = 0;
    // no need to count the last child since the end cut point is implicit
    for (int i = t1.getNumChildren() - 1; i >= 1; --i)
    {
      size = size + utils::getSize(t1[i]);
      base1.sliceAt(size);
    }
  }

  Base base2(width);
  if (t2.getKind() == kind::BITVECTOR_CONCAT)
  {
    unsigned size = 0;
    for (int i = t2.getNumChildren() - 1; i >= 1; --i)
    {
      size = size + utils::getSize(t2[i]);
      base2.sliceAt(size);
    }
  }

  base1.sliceWith(base2);
  if (!base1.isEmpty())
  {
    // we split the equalities according to the base
    int last = 0;
    for (unsigned i = 1; i <= utils::getSize(t1); ++i)
    {
      if (base1.isCutPoint(i))
      {
        Node extract1 = utils::mkExtract(t1, i - 1, last);
        Node extract2 = utils::mkExtract(t2, i - 1, last);
        last = i;
        Assert(utils::getSize(extract1) == utils::getSize(extract2));
        equalities.push_back(nm->mkNode(kind::EQUAL, extract1, extract2));
      }
    }
  }
  else
  {
    // just return same equality
    equalities.push_back(node);
  }
  d_numAddedEqualities += equalities.size() - 1;
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
  smtStatisticsRegistry()->registerStat(&d_numRepresentatives);
  smtStatisticsRegistry()->registerStat(&d_numSplits);
  smtStatisticsRegistry()->registerStat(&d_numMerges);
  smtStatisticsRegistry()->registerStat(&d_avgFindDepth);
  smtStatisticsRegistry()->registerStat(&d_numAddedEqualities);
}

UnionFind::Statistics::~Statistics() {
  smtStatisticsRegistry()->unregisterStat(&d_numRepresentatives);
  smtStatisticsRegistry()->unregisterStat(&d_numSplits);
  smtStatisticsRegistry()->unregisterStat(&d_numMerges);
  smtStatisticsRegistry()->unregisterStat(&d_avgFindDepth);
  smtStatisticsRegistry()->unregisterStat(&d_numAddedEqualities);
}

}  // namespace bv
}  // namespace theory
}  // namespace CVC4
