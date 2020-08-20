/*********************                                                        */
/*! \file theory_arrays.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Clark Barrett, Morgan Deters, Guy Katz
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Implementation of the theory of arrays.
 **
 ** Implementation of the theory of arrays.
 **/

#include "theory/arrays/theory_arrays.h"

#include <map>
#include <memory>

#include "expr/kind.h"
#include "expr/node_algorithm.h"
#include "options/arrays_options.h"
#include "options/smt_options.h"
#include "proof/array_proof.h"
#include "proof/proof_manager.h"
#include "proof/theory_proof.h"
#include "smt/command.h"
#include "smt/logic_exception.h"
#include "smt/smt_statistics_registry.h"
#include "theory/arrays/theory_arrays_rewriter.h"
#include "theory/rewriter.h"
#include "theory/theory_model.h"
#include "theory/valuation.h"

using namespace std;

namespace CVC4 {
namespace theory {
namespace arrays {

// These are the options that produce the best empirical results on QF_AX benchmarks.
// eagerLemmas = true
// eagerIndexSplitting = false

// Use static configuration of options for now
const bool d_ccStore = false;
const bool d_useArrTable = false;
  //const bool d_eagerLemmas = false;
const bool d_preprocess = true;
const bool d_solveWrite = true;
const bool d_solveWrite2 = false;
  // These are now options
  //const bool d_propagateLemmas = true;
  //bool d_useNonLinearOpt = true;
  //bool d_eagerIndexSplitting = false;

TheoryArrays::TheoryArrays(context::Context* c,
                           context::UserContext* u,
                           OutputChannel& out,
                           Valuation valuation,
                           const LogicInfo& logicInfo,
                           ProofNodeManager* pnm,
                           std::string name)
    : Theory(THEORY_ARRAYS, c, u, out, valuation, logicInfo, pnm, name),
      d_numRow(name + "theory::arrays::number of Row lemmas", 0),
      d_numExt(name + "theory::arrays::number of Ext lemmas", 0),
      d_numProp(name + "theory::arrays::number of propagations", 0),
      d_numExplain(name + "theory::arrays::number of explanations", 0),
      d_numNonLinear(name + "theory::arrays::number of calls to setNonLinear",
                     0),
      d_numSharedArrayVarSplits(
          name + "theory::arrays::number of shared array var splits", 0),
      d_numGetModelValSplits(
          name + "theory::arrays::number of getModelVal splits", 0),
      d_numGetModelValConflicts(
          name + "theory::arrays::number of getModelVal conflicts", 0),
      d_numSetModelValSplits(
          name + "theory::arrays::number of setModelVal splits", 0),
      d_numSetModelValConflicts(
          name + "theory::arrays::number of setModelVal conflicts", 0),
      d_ppEqualityEngine(u, name + "theory::arrays::pp", true),
      d_ppFacts(u),
      //      d_ppCache(u),
      d_literalsToPropagate(c),
      d_literalsToPropagateIndex(c, 0),
      d_isPreRegistered(c),
      d_mayEqualEqualityEngine(c, name + "theory::arrays::mayEqual", true),
      d_notify(*this),
      d_conflict(c, false),
      d_backtracker(c),
      d_infoMap(c, &d_backtracker, name),
      d_mergeQueue(c),
      d_mergeInProgress(false),
      d_RowQueue(c),
      d_RowAlreadyAdded(u),
      d_sharedArrays(c),
      d_sharedOther(c),
      d_sharedTerms(c, false),
      d_reads(c),
      d_constReadsList(c),
      d_constReadsContext(new context::Context()),
      d_contextPopper(c, d_constReadsContext),
      d_skolemIndex(c, 0),
      d_decisionRequests(c),
      d_permRef(c),
      d_modelConstraints(c),
      d_lemmasSaved(c),
      d_defValues(c),
      d_readTableContext(new context::Context()),
      d_arrayMerges(c),
      d_inCheckModel(false),
      d_proofReconstruction(nullptr),
      d_dstrat(new TheoryArraysDecisionStrategy(this)),
      d_dstratInit(false)
{
  smtStatisticsRegistry()->registerStat(&d_numRow);
  smtStatisticsRegistry()->registerStat(&d_numExt);
  smtStatisticsRegistry()->registerStat(&d_numProp);
  smtStatisticsRegistry()->registerStat(&d_numExplain);
  smtStatisticsRegistry()->registerStat(&d_numNonLinear);
  smtStatisticsRegistry()->registerStat(&d_numSharedArrayVarSplits);
  smtStatisticsRegistry()->registerStat(&d_numGetModelValSplits);
  smtStatisticsRegistry()->registerStat(&d_numGetModelValConflicts);
  smtStatisticsRegistry()->registerStat(&d_numSetModelValSplits);
  smtStatisticsRegistry()->registerStat(&d_numSetModelValConflicts);

  d_true = NodeManager::currentNM()->mkConst<bool>(true);
  d_false = NodeManager::currentNM()->mkConst<bool>(false);

  // The preprocessing congruence kinds
  d_ppEqualityEngine.addFunctionKind(kind::SELECT);
  d_ppEqualityEngine.addFunctionKind(kind::STORE);
}

TheoryArrays::~TheoryArrays() {
  vector<CTNodeList*>::iterator it = d_readBucketAllocations.begin(), iend = d_readBucketAllocations.end();
  for (; it != iend; ++it) {
    (*it)->deleteSelf();
  }
  delete d_readTableContext;
  CNodeNListMap::iterator it2 = d_constReads.begin();
  for( ; it2 != d_constReads.end(); ++it2 ) {
    it2->second->deleteSelf();
  }
  delete d_constReadsContext;
  smtStatisticsRegistry()->unregisterStat(&d_numRow);
  smtStatisticsRegistry()->unregisterStat(&d_numExt);
  smtStatisticsRegistry()->unregisterStat(&d_numProp);
  smtStatisticsRegistry()->unregisterStat(&d_numExplain);
  smtStatisticsRegistry()->unregisterStat(&d_numNonLinear);
  smtStatisticsRegistry()->unregisterStat(&d_numSharedArrayVarSplits);
  smtStatisticsRegistry()->unregisterStat(&d_numGetModelValSplits);
  smtStatisticsRegistry()->unregisterStat(&d_numGetModelValConflicts);
  smtStatisticsRegistry()->unregisterStat(&d_numSetModelValSplits);
  smtStatisticsRegistry()->unregisterStat(&d_numSetModelValConflicts);
}

TheoryRewriter* TheoryArrays::getTheoryRewriter() { return &d_rewriter; }

bool TheoryArrays::needsEqualityEngine(EeSetupInfo& esi)
{
  esi.d_notify = &d_notify;
  esi.d_name = d_instanceName + "theory::arrays::ee";
  return true;
}

void TheoryArrays::finishInit()
{
  Assert(d_equalityEngine != nullptr);

  // The kinds we are treating as function application in congruence
  d_equalityEngine->addFunctionKind(kind::SELECT);
  if (d_ccStore)
  {
    d_equalityEngine->addFunctionKind(kind::STORE);
  }
  if (d_useArrTable)
  {
    d_equalityEngine->addFunctionKind(kind::ARR_TABLE_FUN);
  }

  d_proofReconstruction.reset(new ArrayProofReconstruction(d_equalityEngine));
  d_reasonRow = d_equalityEngine->getFreshMergeReasonType();
  d_reasonRow1 = d_equalityEngine->getFreshMergeReasonType();
  d_reasonExt = d_equalityEngine->getFreshMergeReasonType();

  d_proofReconstruction->setRowMergeTag(d_reasonRow);
  d_proofReconstruction->setRow1MergeTag(d_reasonRow1);
  d_proofReconstruction->setExtMergeTag(d_reasonExt);

  d_equalityEngine->addPathReconstructionTrigger(d_reasonRow,
                                                 d_proofReconstruction.get());
  d_equalityEngine->addPathReconstructionTrigger(d_reasonRow1,
                                                 d_proofReconstruction.get());
  d_equalityEngine->addPathReconstructionTrigger(d_reasonExt,
                                                 d_proofReconstruction.get());
}

/////////////////////////////////////////////////////////////////////////////
// PREPROCESSING
/////////////////////////////////////////////////////////////////////////////


bool TheoryArrays::ppDisequal(TNode a, TNode b) {
  bool termsExist = d_ppEqualityEngine.hasTerm(a) && d_ppEqualityEngine.hasTerm(b);
  Assert(!termsExist || !a.isConst() || !b.isConst() || a == b
         || d_ppEqualityEngine.areDisequal(a, b, false));
  return ((termsExist && d_ppEqualityEngine.areDisequal(a, b, false)) ||
          Rewriter::rewrite(a.eqNode(b)) == d_false);
}


Node TheoryArrays::solveWrite(TNode term, bool solve1, bool solve2, bool ppCheck)
{
  if (!solve1) {
    return term;
  }
  if (term[0].getKind() != kind::STORE &&
      term[1].getKind() != kind::STORE) {
    return term;
  }
  TNode left = term[0];
  TNode right = term[1];
  int leftWrites = 0, rightWrites = 0;

  // Count nested writes
  TNode e1 = left;
  while (e1.getKind() == kind::STORE) {
    ++leftWrites;
    e1 = e1[0];
  }

  TNode e2 = right;
  while (e2.getKind() == kind::STORE) {
    ++rightWrites;
    e2 = e2[0];
  }

  if (rightWrites > leftWrites) {
    TNode tmp = left;
    left = right;
    right = tmp;
    int tmpWrites = leftWrites;
    leftWrites = rightWrites;
    rightWrites = tmpWrites;
  }

  NodeManager* nm = NodeManager::currentNM();
  if (rightWrites == 0) {
    if (e1 != e2) {
      return term;
    }
    // write(store, index_0, v_0, index_1, v_1, ..., index_n, v_n) = store IFF
    //
    // read(store, index_n) = v_n &
    // index_{n-1} != index_n -> read(store, index_{n-1}) = v_{n-1} &
    // (index_{n-2} != index_{n-1} & index_{n-2} != index_n) -> read(store, index_{n-2}) = v_{n-2} &
    // ...
    // (index_1 != index_2 & ... & index_1 != index_n) -> read(store, index_1) = v_1
    // (index_0 != index_1 & index_0 != index_2 & ... & index_0 != index_n) -> read(store, index_0) = v_0
    TNode write_i, write_j, index_i, index_j;
    Node conc;
    NodeBuilder<> result(kind::AND);
    int i, j;
    write_i = left;
    for (i = leftWrites-1; i >= 0; --i) {
      index_i = write_i[1];

      // build: [index_i /= index_n && index_i /= index_(n-1) &&
      //         ... && index_i /= index_(i+1)] -> read(store, index_i) = v_i
      write_j = left;
      {
        NodeBuilder<> hyp(kind::AND);
        for (j = leftWrites - 1; j > i; --j) {
          index_j = write_j[1];
          if (!ppCheck || !ppDisequal(index_i, index_j)) {
            Node hyp2(index_i.eqNode(index_j));
            hyp << hyp2.notNode();
          }
          write_j = write_j[0];
        }

        Node r1 = nm->mkNode(kind::SELECT, e1, index_i);
        conc = r1.eqNode(write_i[2]);
        if (hyp.getNumChildren() != 0) {
          if (hyp.getNumChildren() == 1) {
            conc = hyp.getChild(0).impNode(conc);
          }
          else {
            r1 = hyp;
            conc = r1.impNode(conc);
          }
        }

        // And into result
        result << conc;

        // Prepare for next iteration
        write_i = write_i[0];
      }
    }
    Assert(result.getNumChildren() > 0);
    if (result.getNumChildren() == 1) {
      return result.getChild(0);
    }
    return result;
  }
  else {
    if (!solve2) {
      return term;
    }
    // store(...) = store(a,i,v) ==>
    // store(store(...),i,select(a,i)) = a && select(store(...),i)=v
    Node l = left;
    Node tmp;
    NodeBuilder<> nb(kind::AND);
    while (right.getKind() == kind::STORE) {
      tmp = nm->mkNode(kind::SELECT, l, right[1]);
      nb << tmp.eqNode(right[2]);
      tmp = nm->mkNode(kind::SELECT, right[0], right[1]);
      l = nm->mkNode(kind::STORE, l, right[1], tmp);
      right = right[0];
    }
    nb << solveWrite(l.eqNode(right), solve1, solve2, ppCheck);
    return nb;
  }
  Unreachable();
  return term;
}

TrustNode TheoryArrays::ppRewrite(TNode term)
{
  if (!d_preprocess)
  {
    return TrustNode::null();
  }
  d_ppEqualityEngine.addTerm(term);
  Node ret;
  switch (term.getKind()) {
    case kind::SELECT: {
      // select(store(a,i,v),j) = select(a,j)
      //    IF i != j
      if (term[0].getKind() == kind::STORE && ppDisequal(term[0][1], term[1])) {
        ret = NodeBuilder<2>(kind::SELECT) << term[0][0] << term[1];
      }
      break;
    }
    case kind::STORE: {
      // store(store(a,i,v),j,w) = store(store(a,j,w),i,v)
      //    IF i != j and j comes before i in the ordering
      if (term[0].getKind() == kind::STORE && (term[1] < term[0][1]) && ppDisequal(term[1],term[0][1])) {
        Node inner = NodeBuilder<3>(kind::STORE) << term[0][0] << term[1] << term[2];
        Node outer = NodeBuilder<3>(kind::STORE) << inner << term[0][1] << term[0][2];
        ret = outer;
      }
      break;
    }
    case kind::EQUAL: {
      ret = solveWrite(term, d_solveWrite, d_solveWrite2, true);
      break;
    }
    default:
      break;
  }
  if (!ret.isNull() && ret != term)
  {
    return TrustNode::mkTrustRewrite(term, ret, nullptr);
  }
  return TrustNode::null();
}


Theory::PPAssertStatus TheoryArrays::ppAssert(TNode in, SubstitutionMap& outSubstitutions) {
  switch(in.getKind()) {
    case kind::EQUAL:
    {
      d_ppFacts.push_back(in);
      d_ppEqualityEngine.assertEquality(in, true, in);
      if (in[0].isVar() && isLegalElimination(in[0], in[1]))
      {
        outSubstitutions.addSubstitution(in[0], in[1]);
        return PP_ASSERT_STATUS_SOLVED;
      }
      if (in[1].isVar() && isLegalElimination(in[1], in[0]))
      {
        outSubstitutions.addSubstitution(in[1], in[0]);
        return PP_ASSERT_STATUS_SOLVED;
      }
      break;
    }
    case kind::NOT:
    {
      d_ppFacts.push_back(in);
      if (in[0].getKind() == kind::EQUAL ) {
        Node a = in[0][0];
        Node b = in[0][1];
        d_ppEqualityEngine.assertEquality(in[0], false, in);
      }
      break;
    }
    default:
      break;
  }
  return PP_ASSERT_STATUS_UNSOLVED;
}


/////////////////////////////////////////////////////////////////////////////
// T-PROPAGATION / REGISTRATION
/////////////////////////////////////////////////////////////////////////////


bool TheoryArrays::propagate(TNode literal)
{
  Debug("arrays") << spaces(getSatContext()->getLevel()) << "TheoryArrays::propagate(" << literal  << ")" << std::endl;

  // If already in conflict, no more propagation
  if (d_conflict) {
    Debug("arrays") << spaces(getSatContext()->getLevel()) << "TheoryArrays::propagate(" << literal << "): already in conflict" << std::endl;
    return false;
  }

  // Propagate away
  if (d_inCheckModel && getSatContext()->getLevel() != d_topLevel) {
    return true;
  }
  bool ok = d_out->propagate(literal);
  if (!ok) {
    d_conflict = true;
  }
  return ok;
}/* TheoryArrays::propagate(TNode) */


void TheoryArrays::explain(TNode literal, std::vector<TNode>& assumptions,
                           eq::EqProof* proof) {
  // Do the work
  bool polarity = literal.getKind() != kind::NOT;
  TNode atom = polarity ? literal : literal[0];
  //eq::EqProof * eqp = new eq::EqProof;
  // eq::EqProof * eqp = NULL;
  if (atom.getKind() == kind::EQUAL) {
    d_equalityEngine->explainEquality(
        atom[0], atom[1], polarity, assumptions, proof);
  } else {
    d_equalityEngine->explainPredicate(atom, polarity, assumptions, proof);
  }
  if (Debug.isOn("pf::array"))
  {
    if (proof)
    {
      Debug("pf::array") << " Proof is : " << std::endl;
      proof->debug_print("pf::array");
    }

    Debug("pf::array") << "Array: explain( " << literal << " ):" << std::endl
                       << "\t";
    for (unsigned i = 0; i < assumptions.size(); ++i)
    {
      Debug("pf::array") << assumptions[i] << " ";
    }
    Debug("pf::array") << std::endl;
  }
}

TNode TheoryArrays::weakEquivGetRep(TNode node) {
  TNode pointer;
  while (true) {
    pointer = d_infoMap.getWeakEquivPointer(node);
    if (pointer.isNull()) {
      return node;
    }
    node = pointer;
  }
}

TNode TheoryArrays::weakEquivGetRepIndex(TNode node, TNode index) {
  Assert(!index.isNull());
  TNode pointer, index2;
  while (true) {
    pointer = d_infoMap.getWeakEquivPointer(node);
    if (pointer.isNull()) {
      return node;
    }
    index2 = d_infoMap.getWeakEquivIndex(node);
    if (index2.isNull() || !d_equalityEngine->areEqual(index, index2))
    {
      node = pointer;
    }
    else {
      TNode secondary = d_infoMap.getWeakEquivSecondary(node);
      if (secondary.isNull()) {
        return node;
      }
      node = secondary;
    }
  }
}

void TheoryArrays::visitAllLeaves(TNode reason, vector<TNode>& conjunctions) {
  switch (reason.getKind()) {
    case kind::AND:
      Assert(reason.getNumChildren() == 2);
      visitAllLeaves(reason[0], conjunctions);
      visitAllLeaves(reason[1], conjunctions);
      break;
    case kind::NOT:
      conjunctions.push_back(reason);
      break;
    case kind::EQUAL:
      d_equalityEngine->explainEquality(
          reason[0], reason[1], true, conjunctions);
      break;
    default:
      Unreachable();
  }
}

void TheoryArrays::weakEquivBuildCond(TNode node, TNode index, vector<TNode>& conjunctions) {
  Assert(!index.isNull());
  TNode pointer, index2;
  while (true) {
    pointer = d_infoMap.getWeakEquivPointer(node);
    if (pointer.isNull()) {
      return;
    }
    index2 = d_infoMap.getWeakEquivIndex(node);
    if (index2.isNull()) {
      // Null index means these two nodes became equal: explain the equality.
      d_equalityEngine->explainEquality(node, pointer, true, conjunctions);
      node = pointer;
    }
    else if (!d_equalityEngine->areEqual(index, index2))
    {
      // If indices are not equal in current context, need to add that to the lemma.
      Node reason = index.eqNode(index2).notNode();
      d_permRef.push_back(reason);
      conjunctions.push_back(reason);
      node = pointer;
    }
    else {
      TNode secondary = d_infoMap.getWeakEquivSecondary(node);
      if (secondary.isNull()) {
        return;
      }
      TNode reason = d_infoMap.getWeakEquivSecondaryReason(node);
      Assert(!reason.isNull());
      visitAllLeaves(reason, conjunctions);
      node = secondary;
    }
  }
}

void TheoryArrays::weakEquivMakeRep(TNode node) {
  TNode pointer = d_infoMap.getWeakEquivPointer(node);
  if (pointer.isNull()) {
    return;
  }
  weakEquivMakeRep(pointer);
  d_infoMap.setWeakEquivPointer(pointer, node);
  d_infoMap.setWeakEquivIndex(pointer, d_infoMap.getWeakEquivIndex(node));
  d_infoMap.setWeakEquivPointer(node, TNode());
  weakEquivMakeRepIndex(node);
}

void TheoryArrays::weakEquivMakeRepIndex(TNode node) {
  TNode secondary = d_infoMap.getWeakEquivSecondary(node);
  if (secondary.isNull()) {
    return;
  }
  TNode index = d_infoMap.getWeakEquivIndex(node);
  Assert(!index.isNull());
  TNode index2 = d_infoMap.getWeakEquivIndex(secondary);
  Node reason;
  TNode next;
  while (index2.isNull() || !d_equalityEngine->areEqual(index, index2))
  {
    next = d_infoMap.getWeakEquivPointer(secondary);
    d_infoMap.setWeakEquivSecondary(node, next);
    reason = d_infoMap.getWeakEquivSecondaryReason(node);
    if (index2.isNull()) {
      reason = reason.andNode(secondary.eqNode(next));
    }
    else {
      reason = reason.andNode(index.eqNode(index2).notNode());
    }
    d_permRef.push_back(reason);
    d_infoMap.setWeakEquivSecondaryReason(node, reason);
    if (next.isNull()) {
      return;
    }
    secondary = next;
    index2 = d_infoMap.getWeakEquivIndex(secondary);
  }
  weakEquivMakeRepIndex(secondary);
  d_infoMap.setWeakEquivSecondary(secondary, node);
  d_infoMap.setWeakEquivSecondaryReason(secondary, d_infoMap.getWeakEquivSecondaryReason(node));
  d_infoMap.setWeakEquivSecondary(node, TNode());
  d_infoMap.setWeakEquivSecondaryReason(node, TNode());
}

void TheoryArrays::weakEquivAddSecondary(TNode index, TNode arrayFrom, TNode arrayTo, TNode reason) {
  std::unordered_set<TNode, TNodeHashFunction> marked;
  vector<TNode> index_trail;
  vector<TNode>::iterator it, iend;
  Node equivalence_trail = reason;
  Node current_reason;
  TNode pointer, indexRep;
  if (!index.isNull()) {
    index_trail.push_back(index);
    marked.insert(d_equalityEngine->getRepresentative(index));
  }
  while (arrayFrom != arrayTo) {
    index = d_infoMap.getWeakEquivIndex(arrayFrom);
    pointer = d_infoMap.getWeakEquivPointer(arrayFrom);
    if (!index.isNull()) {
      indexRep = d_equalityEngine->getRepresentative(index);
      if (marked.find(indexRep) == marked.end() && weakEquivGetRepIndex(arrayFrom, index) != arrayTo) {
        weakEquivMakeRepIndex(arrayFrom);
        d_infoMap.setWeakEquivSecondary(arrayFrom, arrayTo);
        current_reason = equivalence_trail;
        for (it = index_trail.begin(), iend = index_trail.end(); it != iend; ++it) {
          current_reason = current_reason.andNode(index.eqNode(*it).notNode());
        }
        d_permRef.push_back(current_reason);
        d_infoMap.setWeakEquivSecondaryReason(arrayFrom, current_reason);
      }
      marked.insert(indexRep);
    }
    else {
      equivalence_trail = equivalence_trail.andNode(arrayFrom.eqNode(pointer));
    }
    arrayFrom = pointer;
  }
}

void TheoryArrays::checkWeakEquiv(bool arraysMerged) {
  eq::EqClassesIterator eqcs_i = eq::EqClassesIterator(&d_mayEqualEqualityEngine);
  for (; !eqcs_i.isFinished(); ++eqcs_i) {
    Node eqc = (*eqcs_i);
    if (!eqc.getType().isArray()) {
      continue;
    }
    eq::EqClassIterator eqc_i = eq::EqClassIterator(eqc, &d_mayEqualEqualityEngine);
    TNode rep = d_mayEqualEqualityEngine.getRepresentative(*eqc_i);
    TNode weakEquivRep = weakEquivGetRep(rep);
    for (; !eqc_i.isFinished(); ++eqc_i) {
      TNode n = *eqc_i;
      Assert(!arraysMerged || weakEquivGetRep(n) == weakEquivRep);
      TNode pointer = d_infoMap.getWeakEquivPointer(n);
      TNode index = d_infoMap.getWeakEquivIndex(n);
      TNode secondary = d_infoMap.getWeakEquivSecondary(n);
      Assert(pointer.isNull() == (weakEquivGetRep(n) == n));
      Assert(!pointer.isNull() || secondary.isNull());
      Assert(!index.isNull() || secondary.isNull());
      Assert(d_infoMap.getWeakEquivSecondaryReason(n).isNull()
             || !secondary.isNull());
      if (!pointer.isNull()) {
        if (index.isNull()) {
          Assert(d_equalityEngine->areEqual(n, pointer));
        }
        else {
          Assert(
              (n.getKind() == kind::STORE && n[0] == pointer && n[1] == index)
              || (pointer.getKind() == kind::STORE && pointer[0] == n
                  && pointer[1] == index));
        }
      }
    }
  }
}

/**
 * Stores in d_infoMap the following information for each term a of type array:
 *
 *    - all i, such that there exists a term a[i] or a = store(b i v)
 *      (i.e. all indices it is being read atl; store(b i v) is implicitly read at
 *      position i due to the implicit axiom store(b i v)[i] = v )
 *
 *    - all the stores a is congruent to (this information is context dependent)
 *
 *    - all store terms of the form store (a i v) (i.e. in which a appears
 *      directly; this is invariant because no new store terms are created)
 *
 * Note: completeness depends on having pre-register called on all the input
 *       terms before starting to instantiate lemmas.
 */
void TheoryArrays::preRegisterTermInternal(TNode node)
{
  if (d_conflict) {
    return;
  }
  Debug("arrays") << spaces(getSatContext()->getLevel()) << "TheoryArrays::preRegisterTerm(" << node << ")" << std::endl;
  switch (node.getKind()) {
  case kind::EQUAL:
    // Add the trigger for equality
    // NOTE: note that if the equality is true or false already, it might not be added
    d_equalityEngine->addTriggerPredicate(node);
    break;
  case kind::SELECT: {
    // Invariant: array terms should be preregistered before being added to the equality engine
    if (d_equalityEngine->hasTerm(node))
    {
      Assert(d_isPreRegistered.find(node) != d_isPreRegistered.end());
      return;
    }
    // Reads
    TNode store = d_equalityEngine->getRepresentative(node[0]);

    // The may equal needs the store
    d_mayEqualEqualityEngine.addTerm(store);

    if (node.getType().isArray())
    {
      d_mayEqualEqualityEngine.addTerm(node);
      d_equalityEngine->addTriggerTerm(node, THEORY_ARRAYS);
    }
    else
    {
      d_equalityEngine->addTerm(node);
    }
    Assert((d_isPreRegistered.insert(node), true));

    Assert(d_equalityEngine->getRepresentative(store) == store);
    d_infoMap.addIndex(store, node[1]);

    // Synchronize d_constReadsContext with SAT context
    Assert(d_constReadsContext->getLevel() <= getSatContext()->getLevel());
    while (d_constReadsContext->getLevel() < getSatContext()->getLevel()) {
      d_constReadsContext->push();
    }

    // Record read in sharing data structure
    TNode index = d_equalityEngine->getRepresentative(node[1]);
    if (!options::arraysWeakEquivalence() && index.isConst()) {
      CTNodeList* temp;
      CNodeNListMap::iterator it = d_constReads.find(index);
      if (it == d_constReads.end()) {
        temp = new(true) CTNodeList(d_constReadsContext);
        d_constReads[index] = temp;
      }
      else {
        temp = (*it).second;
      }
      temp->push_back(node);
      d_constReadsList.push_back(node);
    }
    else {
      d_reads.push_back(node);
    }

    checkRowForIndex(node[1], store);
    break;
  }
  case kind::STORE: {
    if (d_equalityEngine->hasTerm(node))
    {
      break;
    }
    d_equalityEngine->addTriggerTerm(node, THEORY_ARRAYS);

    TNode a = d_equalityEngine->getRepresentative(node[0]);

    if (node.isConst()) {
      // Can't use d_mayEqualEqualityEngine to merge node with a because they are both constants,
      // so just set the default value manually for node.
      Assert(a == node[0]);
      d_mayEqualEqualityEngine.addTerm(node);
      Assert(d_mayEqualEqualityEngine.getRepresentative(node) == node);
      Assert(d_mayEqualEqualityEngine.getRepresentative(a) == a);
      DefValMap::iterator it = d_defValues.find(a);
      Assert(it != d_defValues.end());
      d_defValues[node] = (*it).second;
    }
    else {
      d_mayEqualEqualityEngine.assertEquality(node.eqNode(a), true, d_true);
      Assert(d_mayEqualEqualityEngine.consistent());
    }

    TNode i = node[1];
    TNode v = node[2];
    NodeManager* nm = NodeManager::currentNM();
    Node ni = nm->mkNode(kind::SELECT, node, i);
    if (!d_equalityEngine->hasTerm(ni))
    {
      preRegisterTermInternal(ni);
    }

    // Apply RIntro1 Rule
    d_equalityEngine->assertEquality(ni.eqNode(v), true, d_true, d_reasonRow1);

    d_infoMap.addStore(node, node);
    d_infoMap.addInStore(a, node);
    d_infoMap.setModelRep(node, node);

    //Add-Store for Weak Equivalence
    if (options::arraysWeakEquivalence()) {
      Assert(weakEquivGetRep(node[0]) == weakEquivGetRep(a));
      Assert(weakEquivGetRep(node) == node);
      d_infoMap.setWeakEquivPointer(node, node[0]);
      d_infoMap.setWeakEquivIndex(node, node[1]);
#ifdef CVC4_ASSERTIONS
      checkWeakEquiv(false);
#endif
    }

    checkStore(node);
    break;
  }
  case kind::STORE_ALL: {
    if (d_equalityEngine->hasTerm(node))
    {
      break;
    }
    ArrayStoreAll storeAll = node.getConst<ArrayStoreAll>();
    Node defaultValue = storeAll.getValue();
    if (!defaultValue.isConst()) {
      throw LogicException("Array theory solver does not yet support non-constant default values for arrays");
    }
    d_infoMap.setConstArr(node, node);
    d_mayEqualEqualityEngine.addTerm(node);
    Assert(d_mayEqualEqualityEngine.getRepresentative(node) == node);
    d_equalityEngine->addTriggerTerm(node, THEORY_ARRAYS);
    d_defValues[node] = defaultValue;
    break;
  }
  default:
    // Variables etc
    if (node.getType().isArray()) {
      // The may equal needs the node
      d_mayEqualEqualityEngine.addTerm(node);
      d_equalityEngine->addTriggerTerm(node, THEORY_ARRAYS);
      Assert(d_equalityEngine->getSize(node) == 1);
    }
    else {
      d_equalityEngine->addTerm(node);
    }

    break;
  }
  // Invariant: preregistered terms are exactly the terms in the equality engine
  // Disabled, see comment above for kind::EQUAL
  // Assert(d_equalityEngine->hasTerm(node) ||
  // !d_equalityEngine->consistent());
}


void TheoryArrays::preRegisterTerm(TNode node)
{
  preRegisterTermInternal(node);
  // If we have a select from an array of Bools, mark it as a term that can be propagated.
  // Note: do this here instead of in preRegisterTermInternal to prevent internal select
  // terms from being propagated out (as this results in an assertion failure).
  if (node.getKind() == kind::SELECT && node.getType().isBoolean()) {
    d_equalityEngine->addTriggerPredicate(node);
  }
}


void TheoryArrays::propagate(Effort e)
{
  // direct propagation now
}

TrustNode TheoryArrays::explain(TNode literal)
{
  Node explanation = explain(literal, NULL);
  return TrustNode::mkTrustPropExp(literal, explanation, nullptr);
}

Node TheoryArrays::explain(TNode literal, eq::EqProof* proof) {
  ++d_numExplain;
  Debug("arrays") << spaces(getSatContext()->getLevel())
                  << "TheoryArrays::explain(" << literal << ")" << std::endl;
  std::vector<TNode> assumptions;
  explain(literal, assumptions, proof);
  return mkAnd(assumptions);
}

/////////////////////////////////////////////////////////////////////////////
// SHARING
/////////////////////////////////////////////////////////////////////////////


void TheoryArrays::addSharedTerm(TNode t) {
  Debug("arrays::sharing") << spaces(getSatContext()->getLevel()) << "TheoryArrays::addSharedTerm(" << t << ")" << std::endl;
  d_equalityEngine->addTriggerTerm(t, THEORY_ARRAYS);
  if (t.getType().isArray()) {
    d_sharedArrays.insert(t);
  }
  else {
#ifdef CVC4_ASSERTIONS
    d_sharedOther.insert(t);
#endif
    d_sharedTerms = true;
  }
}


EqualityStatus TheoryArrays::getEqualityStatus(TNode a, TNode b) {
  Assert(d_equalityEngine->hasTerm(a) && d_equalityEngine->hasTerm(b));
  if (d_equalityEngine->areEqual(a, b))
  {
    // The terms are implied to be equal
    return EQUALITY_TRUE;
  }
  else if (d_equalityEngine->areDisequal(a, b, false))
  {
    // The terms are implied to be dis-equal
    return EQUALITY_FALSE;
  }
  return EQUALITY_UNKNOWN;//FALSE_IN_MODEL;
}


void TheoryArrays::checkPair(TNode r1, TNode r2)
{
  Debug("arrays::sharing") << "TheoryArrays::computeCareGraph(): checking reads " << r1 << " and " << r2 << std::endl;

  TNode x = r1[1];
  TNode y = r2[1];
  Assert(d_equalityEngine->isTriggerTerm(x, THEORY_ARRAYS));

  if (d_equalityEngine->hasTerm(x) && d_equalityEngine->hasTerm(y)
      && (d_equalityEngine->areEqual(x, y)
          || d_equalityEngine->areDisequal(x, y, false)))
  {
    Debug("arrays::sharing") << "TheoryArrays::computeCareGraph(): equality known, skipping" << std::endl;
    return;
  }

  // If the terms are already known to be equal, we are also in good shape
  if (d_equalityEngine->areEqual(r1, r2))
  {
    Debug("arrays::sharing") << "TheoryArrays::computeCareGraph(): equal, skipping" << std::endl;
    return;
  }

  if (r1[0] != r2[0]) {
    // If arrays are known to be disequal, or cannot become equal, we can continue
    Assert(d_mayEqualEqualityEngine.hasTerm(r1[0])
           && d_mayEqualEqualityEngine.hasTerm(r2[0]));
    if (r1[0].getType() != r2[0].getType()
        || d_equalityEngine->areDisequal(r1[0], r2[0], false))
    {
      Debug("arrays::sharing") << "TheoryArrays::computeCareGraph(): arrays can't be equal, skipping" << std::endl;
      return;
    }
    else if (!d_mayEqualEqualityEngine.areEqual(r1[0], r2[0])) {
      return;
    }
  }

  if (!d_equalityEngine->isTriggerTerm(y, THEORY_ARRAYS))
  {
    Debug("arrays::sharing") << "TheoryArrays::computeCareGraph(): not connected to shared terms, skipping" << std::endl;
    return;
  }

  // Get representative trigger terms
  TNode x_shared =
      d_equalityEngine->getTriggerTermRepresentative(x, THEORY_ARRAYS);
  TNode y_shared =
      d_equalityEngine->getTriggerTermRepresentative(y, THEORY_ARRAYS);
  EqualityStatus eqStatusDomain = d_valuation.getEqualityStatus(x_shared, y_shared);
  switch (eqStatusDomain) {
    case EQUALITY_TRUE_AND_PROPAGATED:
      // Should have been propagated to us
      Assert(false);
      break;
    case EQUALITY_TRUE:
      // Missed propagation - need to add the pair so that theory engine can force propagation
      Debug("arrays::sharing") << "TheoryArrays::computeCareGraph(): missed propagation" << std::endl;
      break;
    case EQUALITY_FALSE_AND_PROPAGATED:
      // Should have been propagated to us
      Assert(false);
    case EQUALITY_FALSE:
    case EQUALITY_FALSE_IN_MODEL:
      // This is unlikely, but I think it could happen
      Debug("arrays::sharing") << "TheoryArrays::computeCareGraph(): checkPair called when false in model" << std::endl;
      return;
    default:
      // Covers EQUALITY_TRUE_IN_MODEL (common case) and EQUALITY_UNKNOWN
      break;
  }

  // Add this pair
  Debug("arrays::sharing") << "TheoryArrays::computeCareGraph(): adding to care-graph" << std::endl;
  addCarePair(x_shared, y_shared);
}


void TheoryArrays::computeCareGraph()
{
  if (d_sharedArrays.size() > 0) {
    CDNodeSet::key_iterator it1 = d_sharedArrays.key_begin(), it2, iend = d_sharedArrays.key_end();
    for (; it1 != iend; ++it1) {
      for (it2 = it1, ++it2; it2 != iend; ++it2) {
        if ((*it1).getType() != (*it2).getType()) {
          continue;
        }
        EqualityStatus eqStatusArr = getEqualityStatus((*it1), (*it2));
        if (eqStatusArr != EQUALITY_UNKNOWN) {
          continue;
        }
        Assert(d_valuation.getEqualityStatus((*it1), (*it2))
               == EQUALITY_UNKNOWN);
        addCarePair((*it1), (*it2));
        ++d_numSharedArrayVarSplits;
        return;
      }
    }
  }
  if (d_sharedTerms) {
    // Synchronize d_constReadsContext with SAT context
    Assert(d_constReadsContext->getLevel() <= getSatContext()->getLevel());
    while (d_constReadsContext->getLevel() < getSatContext()->getLevel()) {
      d_constReadsContext->push();
    }

    // Go through the read terms and see if there are any to split on

    // Give constReadsContext a push so that all the work it does here is erased - models can change if context changes at all
    // The context is popped at the end.  If this loop is interrupted for some reason, we have to make sure the context still
    // gets popped or the solver will be in an inconsistent state
    d_constReadsContext->push();
    unsigned size = d_reads.size();
    for (unsigned i = 0; i < size; ++ i) {
      TNode r1 = d_reads[i];

      Debug("arrays::sharing") << "TheoryArrays::computeCareGraph(): checking read " << r1 << std::endl;
      Assert(d_equalityEngine->hasTerm(r1));
      TNode x = r1[1];

      if (!d_equalityEngine->isTriggerTerm(x, THEORY_ARRAYS))
      {
        Debug("arrays::sharing") << "TheoryArrays::computeCareGraph(): not connected to shared terms, skipping" << std::endl;
        continue;
      }
      Node x_shared =
          d_equalityEngine->getTriggerTermRepresentative(x, THEORY_ARRAYS);

      // Get the model value of index and find all reads that read from that same model value: these are the pairs we have to check
      // Also, insert this read in the list at the proper index

      if (!x_shared.isConst()) {
        x_shared = d_valuation.getModelValue(x_shared);
      }
      if (!x_shared.isNull()) {
        CTNodeList* temp;
        CNodeNListMap::iterator it = d_constReads.find(x_shared);
        if (it == d_constReads.end()) {
          // This is the only x_shared with this model value - no need to create any splits
          temp = new(true) CTNodeList(d_constReadsContext);
          d_constReads[x_shared] = temp;
        }
        else {
          temp = (*it).second;
          for (size_t j = 0; j < temp->size(); ++j) {
            checkPair(r1, (*temp)[j]);
          }
        }
        temp->push_back(r1);
      }
      else {
        // We don't know the model value for x.  Just do brute force examination of all pairs of reads
        for (unsigned j = 0; j < size; ++j) {
          TNode r2 = d_reads[j];
          Assert(d_equalityEngine->hasTerm(r2));
          checkPair(r1,r2);
        }
        for (unsigned j = 0; j < d_constReadsList.size(); ++j) {
          TNode r2 = d_constReadsList[j];
          Assert(d_equalityEngine->hasTerm(r2));
          checkPair(r1,r2);
        }
      }
    }
    d_constReadsContext->pop();
  }
}


/////////////////////////////////////////////////////////////////////////////
// MODEL GENERATION
/////////////////////////////////////////////////////////////////////////////

bool TheoryArrays::collectModelInfo(TheoryModel* m)
{
  // Compute terms appearing in assertions and shared terms, and also
  // include additional reads due to the RIntro1 and RIntro2 rules.
  std::set<Node> termSet;
  computeRelevantTerms(termSet);

  // Send the equality engine information to the model
  if (!m->assertEqualityEngine(d_equalityEngine, &termSet))
  {
    return false;
  }

  NodeManager* nm = NodeManager::currentNM();
  // Compute arrays that we need to produce representatives for
  std::vector<Node> arrays;
  eq::EqClassesIterator eqcs_i = eq::EqClassesIterator(d_equalityEngine);
  for (; !eqcs_i.isFinished(); ++eqcs_i) {
    Node eqc = (*eqcs_i);
    if (!eqc.getType().isArray())
    {
      // not an array, skip
      continue;
    }
    eq::EqClassIterator eqc_i = eq::EqClassIterator(eqc, d_equalityEngine);
    for (; !eqc_i.isFinished(); ++eqc_i) {
      Node n = *eqc_i;
      // If this EC is an array type and it contains something other than STORE nodes, we have to compute a representative explicitly
      if (termSet.find(n) != termSet.end())
      {
        if (n.getKind() != kind::STORE)
        {
          arrays.push_back(n);
          break;
        }
      }
    }
  }

  // Build a list of all the relevant reads, indexed by the store representative
  std::map<Node, std::vector<Node> > selects;
  set<Node>::iterator set_it = termSet.begin(), set_it_end = termSet.end();
  for (; set_it != set_it_end; ++set_it) {
    Node n = *set_it;
    // If this term is a select, record that the EC rep of its store parameter is being read from using this term
    if (n.getKind() == kind::SELECT) {
      selects[d_equalityEngine->getRepresentative(n[0])].push_back(n);
    }
  }

  Node rep;
  DefValMap::iterator it;
  TypeSet defaultValuesSet;

  // Compute all default values already in use
  //if (fullModel) {
    for (size_t i=0; i<arrays.size(); ++i) {
      TNode nrep = d_equalityEngine->getRepresentative(arrays[i]);
      d_mayEqualEqualityEngine.addTerm(nrep); // add the term in case it isn't there already
      TNode mayRep = d_mayEqualEqualityEngine.getRepresentative(nrep);
      it = d_defValues.find(mayRep);
      if (it != d_defValues.end()) {
        defaultValuesSet.add(nrep.getType().getArrayConstituentType(), (*it).second);
      }
    }
  //}

  // Loop through all array equivalence classes that need a representative computed
  for (size_t i=0; i<arrays.size(); ++i) {
    TNode n = arrays[i];
    TNode nrep = d_equalityEngine->getRepresentative(n);

    //if (fullModel) {
      // Compute default value for this array - there is one default value for every mayEqual equivalence class
      TNode mayRep = d_mayEqualEqualityEngine.getRepresentative(nrep);
      it = d_defValues.find(mayRep);
      // If this mayEqual EC doesn't have a default value associated, get the next available default value for the associated array element type
      if (it == d_defValues.end()) {
        TypeNode valueType = nrep.getType().getArrayConstituentType();
        rep = defaultValuesSet.nextTypeEnum(valueType);
        if (rep.isNull()) {
          Assert(defaultValuesSet.getSet(valueType)->begin()
                 != defaultValuesSet.getSet(valueType)->end());
          rep = *(defaultValuesSet.getSet(valueType)->begin());
        }
        Trace("arrays-models") << "New default value = " << rep << endl;
        d_defValues[mayRep] = rep;
      }
      else {
        rep = (*it).second;
      }

      // Build the STORE_ALL term with the default value
      rep = nm->mkConst(ArrayStoreAll(nrep.getType(), rep));
      /*
    }
    else {
      std::unordered_map<Node, Node, NodeHashFunction>::iterator it = d_skolemCache.find(n);
      if (it == d_skolemCache.end()) {
        rep = nm->mkSkolem("array_collect_model_var", n.getType(), "base model variable for array collectModelInfo");
        d_skolemCache[n] = rep;
      }
      else {
        rep = (*it).second;
      }
    }
*/

    // For each read, require that the rep stores the right value
    vector<Node>& reads = selects[nrep];
    for (unsigned j = 0; j < reads.size(); ++j) {
      rep = nm->mkNode(kind::STORE, rep, reads[j][1], reads[j]);
    }
    if (!m->assertEquality(n, rep, true))
    {
      return false;
    }
    if (!n.isConst()) {
      m->assertSkeleton(rep);
    }
  }
  return true;
}

/////////////////////////////////////////////////////////////////////////////
// NOTIFICATIONS
/////////////////////////////////////////////////////////////////////////////


void TheoryArrays::presolve()
{
  Trace("arrays")<<"Presolving \n";
  if (!d_dstratInit)
  {
    d_dstratInit = true;
    // add the decision strategy, which is user-context-independent
    getDecisionManager()->registerStrategy(
        DecisionManager::STRAT_ARRAYS,
        d_dstrat.get(),
        DecisionManager::STRAT_SCOPE_CTX_INDEPENDENT);
  }
}


/////////////////////////////////////////////////////////////////////////////
// MAIN SOLVER
/////////////////////////////////////////////////////////////////////////////


Node TheoryArrays::getSkolem(TNode ref, const string& name, const TypeNode& type, const string& comment, bool makeEqual)
{
  Node skolem;
  std::unordered_map<Node, Node, NodeHashFunction>::iterator it = d_skolemCache.find(ref);
  if (it == d_skolemCache.end()) {
    NodeManager* nm = NodeManager::currentNM();
    skolem = nm->mkSkolem(name, type, comment);
    d_skolemCache[ref] = skolem;
  }
  else {
    skolem = (*it).second;
    if (d_equalityEngine->hasTerm(ref) && d_equalityEngine->hasTerm(skolem)
        && d_equalityEngine->areEqual(ref, skolem))
    {
      makeEqual = false;
    }
  }

  Debug("pf::array") << "Pregistering a Skolem" << std::endl;
  preRegisterTermInternal(skolem);
  Debug("pf::array") << "Pregistering a Skolem DONE" << std::endl;

  if (makeEqual) {
    Node d = skolem.eqNode(ref);
    Debug("arrays-model-based") << "Asserting skolem equality " << d << endl;
    d_equalityEngine->assertEquality(d, true, d_true);
    Assert(!d_conflict);
    d_skolemAssertions.push_back(d);
    d_skolemIndex = d_skolemIndex + 1;
  }

  Debug("pf::array") << "getSkolem DONE" << std::endl;
  return skolem;
}


void TheoryArrays::check(Effort e) {
  if (done() && !fullEffort(e)) {
    return;
  }

  getOutputChannel().spendResource(ResourceManager::Resource::TheoryCheckStep);

  TimerStat::CodeTimer checkTimer(d_checkTime);

  while (!done() && !d_conflict)
  {
    // Get all the assertions
    Assertion assertion = get();
    TNode fact = assertion.d_assertion;

    Debug("arrays") << spaces(getSatContext()->getLevel()) << "TheoryArrays::check(): processing " << fact << std::endl;

    bool polarity = fact.getKind() != kind::NOT;
    TNode atom = polarity ? fact : fact[0];

    if (!assertion.d_isPreregistered)
    {
      if (atom.getKind() == kind::EQUAL) {
        if (!d_equalityEngine->hasTerm(atom[0]))
        {
          Assert(atom[0].isConst());
          d_equalityEngine->addTerm(atom[0]);
        }
        if (!d_equalityEngine->hasTerm(atom[1]))
        {
          Assert(atom[1].isConst());
          d_equalityEngine->addTerm(atom[1]);
        }
      }
    }

    // Do the work
    switch (fact.getKind()) {
      case kind::EQUAL:
        d_equalityEngine->assertEquality(fact, true, fact);
        break;
      case kind::SELECT:
        d_equalityEngine->assertPredicate(fact, true, fact);
        break;
      case kind::NOT:
        if (fact[0].getKind() == kind::SELECT) {
          d_equalityEngine->assertPredicate(fact[0], false, fact);
        }
        else if (!d_equalityEngine->areDisequal(fact[0][0], fact[0][1], false))
        {
          // Assert the dis-equality
          d_equalityEngine->assertEquality(fact[0], false, fact);

          // Apply ArrDiseq Rule if diseq is between arrays
          if(fact[0][0].getType().isArray() && !d_conflict) {
            if (d_conflict) { Debug("pf::array") << "Entering the skolemization branch" << std::endl; }

            NodeManager* nm = NodeManager::currentNM();
            TypeNode indexType = fact[0][0].getType()[0];

            TNode k;
            // k is the skolem for this disequality.
            if (!d_proofsEnabled) {
              Debug("pf::array") << "Check: kind::NOT: array theory making a skolem" << std::endl;

              // If not in replay mode, generate a fresh skolem variable
              k = getSkolem(fact,
                            "array_ext_index",
                            indexType,
                            "an extensional lemma index variable from the theory of arrays",
                            false);

              // Register this skolem for the proof replay phase
              PROOF(ProofManager::getSkolemizationManager()->registerSkolem(fact, k));
            } else {
              if (!ProofManager::getSkolemizationManager()->hasSkolem(fact)) {
                // In the solution pass we didn't need this skolem. Therefore, we don't need it
                // in this reply pass, either.
                break;
              }

              // Reuse the same skolem as in the solution pass
              k = ProofManager::getSkolemizationManager()->getSkolem(fact);
              Debug("pf::array") << "Skolem = " << k << std::endl;
            }

            Node ak = nm->mkNode(kind::SELECT, fact[0][0], k);
            Node bk = nm->mkNode(kind::SELECT, fact[0][1], k);
            Node eq = ak.eqNode(bk);
            Node lemma = fact[0].orNode(eq.notNode());

            // In solve mode we don't care if ak and bk are registered. If they aren't, they'll be registered
            // when we output the lemma. However, in replay need the lemma to be propagated, and so we
            // preregister manually.
            if (d_proofsEnabled) {
              if (!d_equalityEngine->hasTerm(ak))
              {
                preRegisterTermInternal(ak);
              }
              if (!d_equalityEngine->hasTerm(bk))
              {
                preRegisterTermInternal(bk);
              }
            }

            if (options::arraysPropagate() > 0 && d_equalityEngine->hasTerm(ak)
                && d_equalityEngine->hasTerm(bk))
            {
              // Propagate witness disequality - might produce a conflict
              d_permRef.push_back(lemma);
              Debug("pf::array") << "Asserting to the equality engine:" << std::endl
                                 << "\teq = " << eq << std::endl
                                 << "\treason = " << fact << std::endl;

              d_equalityEngine->assertEquality(eq, false, fact, d_reasonExt);
              ++d_numProp;
            }

            if (!d_proofsEnabled) {
              // If this is the solution pass, generate the lemma. Otherwise, don't generate it -
              // as this is the lemma that we're reproving...
              Trace("arrays-lem")<<"Arrays::addExtLemma " << lemma <<"\n";
              d_out->lemma(lemma);
              ++d_numExt;
            }
          } else {
            Debug("pf::array") << "Check: kind::NOT: array theory NOT making a skolem" << std::endl;
            d_modelConstraints.push_back(fact);
          }
        }
        break;
    default:
      Unreachable();
      break;
    }
  }

  if ((options::arraysEagerLemmas() || fullEffort(e)) && !d_conflict && options::arraysWeakEquivalence()) {
    // Replay all array merges to update weak equivalence data structures
    context::CDList<Node>::iterator it = d_arrayMerges.begin(), iend = d_arrayMerges.end();
    TNode a, b, eq;
    for (; it != iend; ++it) {
      eq = *it;
      a = eq[0];
      b = eq[1];
      weakEquivMakeRep(b);
      if (weakEquivGetRep(a) == b) {
        weakEquivAddSecondary(TNode(), a, b, eq);
      }
      else {
        d_infoMap.setWeakEquivPointer(b, a);
        d_infoMap.setWeakEquivIndex(b, TNode());
      }
#ifdef CVC4_ASSERTIONS
    checkWeakEquiv(false);
#endif
    }
#ifdef CVC4_ASSERTIONS
    checkWeakEquiv(true);
#endif

    d_readTableContext->push();
    TNode mayRep, iRep;
    CTNodeList* bucketList = NULL;
    CTNodeList::const_iterator i = d_reads.begin(), readsEnd = d_reads.end();
    for (; i != readsEnd; ++i) {
      const TNode& r = *i;

      Debug("arrays::weak") << "TheoryArrays::check(): checking read " << r << std::endl;

      // Find the bucket for this read.
      mayRep = d_mayEqualEqualityEngine.getRepresentative(r[0]);
      iRep = d_equalityEngine->getRepresentative(r[1]);
      std::pair<TNode, TNode> key(mayRep, iRep);
      ReadBucketMap::iterator rbm_it = d_readBucketTable.find(key);
      if (rbm_it == d_readBucketTable.end())
      {
        bucketList = new(true) CTNodeList(d_readTableContext);
        d_readBucketAllocations.push_back(bucketList);
        d_readBucketTable[key] = bucketList;
      }
      else {
        bucketList = rbm_it->second;
      }
      CTNodeList::const_iterator ctnl_it = bucketList->begin(),
                                 ctnl_iend = bucketList->end();
      for (; ctnl_it != ctnl_iend; ++ctnl_it)
      {
        const TNode& r2 = *ctnl_it;
        Assert(r2.getKind() == kind::SELECT);
        Assert(mayRep == d_mayEqualEqualityEngine.getRepresentative(r2[0]));
        Assert(iRep == d_equalityEngine->getRepresentative(r2[1]));
        if (d_equalityEngine->areEqual(r, r2))
        {
          continue;
        }
        if (weakEquivGetRepIndex(r[0], r[1]) == weakEquivGetRepIndex(r2[0], r[1])) {
          // add lemma: r[1] = r2[1] /\ cond(r[0],r2[0]) => r = r2
          vector<TNode> conjunctions;
          Assert(d_equalityEngine->areEqual(r, Rewriter::rewrite(r)));
          Assert(d_equalityEngine->areEqual(r2, Rewriter::rewrite(r2)));
          Node lemma = Rewriter::rewrite(r).eqNode(Rewriter::rewrite(r2)).negate();
          d_permRef.push_back(lemma);
          conjunctions.push_back(lemma);
          if (r[1] != r2[1]) {
            d_equalityEngine->explainEquality(r[1], r2[1], true, conjunctions);
          }
          // TODO: get smaller lemmas by eliminating shared parts of path
          weakEquivBuildCond(r[0], r[1], conjunctions);
          weakEquivBuildCond(r2[0], r[1], conjunctions);
          lemma = mkAnd(conjunctions, true);
          // LSH FIXME: which kind of arrays lemma is this
          Trace("arrays-lem") << "Arrays::addExtLemma " << lemma <<"\n";
          d_out->lemma(lemma, RULE_INVALID, LemmaProperty::SEND_ATOMS);
          d_readTableContext->pop();
          Trace("arrays") << spaces(getSatContext()->getLevel()) << "Arrays::check(): done" << endl;
          return;
        }
      }
      bucketList->push_back(r);
    }
    d_readTableContext->pop();
  }

  if(!options::arraysEagerLemmas() && fullEffort(e) && !d_conflict && !options::arraysWeakEquivalence()) {
    // generate the lemmas on the worklist
    Trace("arrays-lem")<< "Arrays::discharging lemmas. Number of queued lemmas: " << d_RowQueue.size() << "\n";
    while (d_RowQueue.size() > 0 && !d_conflict) {
      if (dischargeLemmas()) {
        break;
      }
    }
  }

  Trace("arrays") << spaces(getSatContext()->getLevel()) << "Arrays::check(): done" << endl;
}


Node TheoryArrays::mkAnd(std::vector<TNode>& conjunctions, bool invert, unsigned startIndex)
{
  if (conjunctions.empty())
  {
    return invert ? d_false : d_true;
  }

  std::set<TNode> all;

  unsigned i = startIndex;
  TNode t;
  for (; i < conjunctions.size(); ++i) {
    t = conjunctions[i];
    if (t == d_true) {
      continue;
    }
    else if (t.getKind() == kind::AND) {
      for(TNode::iterator child_it = t.begin(); child_it != t.end(); ++child_it) {
        if (*child_it == d_true) {
          continue;
        }
        all.insert(*child_it);
      }
    }
    else {
      all.insert(t);
    }
  }

  if (all.size() == 0) {
    return invert ? d_false : d_true;
  }
  if (all.size() == 1) {
    // All the same, or just one
    if (invert) {
      return (*(all.begin())).negate();
    }
    else {
      return *(all.begin());
    }
  }

  NodeBuilder<> conjunction(invert ? kind::OR : kind::AND);
  std::set<TNode>::const_iterator it = all.begin();
  std::set<TNode>::const_iterator it_end = all.end();
  while (it != it_end) {
    if (invert) {
      conjunction << (*it).negate();
    }
    else {
      conjunction << *it;
    }
    ++ it;
  }

  return conjunction;
}


void TheoryArrays::setNonLinear(TNode a)
{
  if (options::arraysWeakEquivalence()) return;
  if (d_infoMap.isNonLinear(a)) return;

  Trace("arrays") << spaces(getSatContext()->getLevel()) << "Arrays::setNonLinear (" << a << ")\n";
  d_infoMap.setNonLinear(a);
  ++d_numNonLinear;

  const CTNodeList* i_a = d_infoMap.getIndices(a);
  const CTNodeList* st_a = d_infoMap.getStores(a);
  const CTNodeList* inst_a = d_infoMap.getInStores(a);

  size_t it = 0;

  // Propagate non-linearity down chain of stores
  for( ; it < st_a->size(); ++it) {
    TNode store = (*st_a)[it];
    Assert(store.getKind() == kind::STORE);
    setNonLinear(store[0]);
  }

  // Instantiate ROW lemmas that were ignored before
  size_t it2 = 0;
  RowLemmaType lem;
  for(; it2 < i_a->size(); ++it2) {
    TNode i = (*i_a)[it2];
    it = 0;
    for ( ; it < inst_a->size(); ++it) {
      TNode store = (*inst_a)[it];
      Assert(store.getKind() == kind::STORE);
      TNode j = store[1];
      TNode c = store[0];
      lem = std::make_tuple(store, c, j, i);
      Trace("arrays-lem") << spaces(getSatContext()->getLevel()) <<"Arrays::setNonLinear ("<<store<<", "<<c<<", "<<j<<", "<<i<<")\n";
      queueRowLemma(lem);
    }
  }

}

void TheoryArrays::mergeArrays(TNode a, TNode b)
{
  // Note: a is the new representative
  Assert(a.getType().isArray() && b.getType().isArray());

  if (d_mergeInProgress) {
    // Nested call to mergeArrays, just push on the queue and return
    d_mergeQueue.push(a.eqNode(b));
    return;
  }

  d_mergeInProgress = true;

  Node n;
  while (true) {
    // Normally, a is its own representative, but it's possible for a to have
    // been merged with another array after it got queued up by the equality engine,
    // so we take its representative to be safe.
    a = d_equalityEngine->getRepresentative(a);
    Assert(d_equalityEngine->getRepresentative(b) == a);
    Trace("arrays-merge") << spaces(getSatContext()->getLevel()) << "Arrays::merge: (" << a << ", " << b << ")\n";

    if (options::arraysOptimizeLinear() && !options::arraysWeakEquivalence()) {
      bool aNL = d_infoMap.isNonLinear(a);
      bool bNL = d_infoMap.isNonLinear(b);
      if (aNL) {
        if (bNL) {
          // already both marked as non-linear - no need to do anything
        }
        else {
          // Set b to be non-linear
          setNonLinear(b);
        }
      }
      else {
        if (bNL) {
          // Set a to be non-linear
          setNonLinear(a);
        }
        else {
          // Check for new non-linear arrays
          const CTNodeList* astores = d_infoMap.getStores(a);
          const CTNodeList* bstores = d_infoMap.getStores(b);
          Assert(astores->size() <= 1 && bstores->size() <= 1);
          if (astores->size() > 0 && bstores->size() > 0) {
            setNonLinear(a);
            setNonLinear(b);
          }
        }
      }
    }

    TNode constArrA = d_infoMap.getConstArr(a);
    TNode constArrB = d_infoMap.getConstArr(b);
    if (constArrA.isNull()) {
      if (!constArrB.isNull()) {
        d_infoMap.setConstArr(a,constArrB);
      }
    }
    else if (!constArrB.isNull()) {
      if (constArrA != constArrB) {
        conflict(constArrA,constArrB);
      }
    }

    TNode mayRepA = d_mayEqualEqualityEngine.getRepresentative(a);
    TNode mayRepB = d_mayEqualEqualityEngine.getRepresentative(b);

    // If a and b have different default values associated with their mayequal equivalence classes,
    // things get complicated.  Similarly, if two mayequal equivalence classes have different
    // constant representatives, it's not clear what to do. - disallow these cases for now.  -Clark
    DefValMap::iterator it = d_defValues.find(mayRepA);
    DefValMap::iterator it2 = d_defValues.find(mayRepB);
    TNode defValue;

    if (it != d_defValues.end()) {
      defValue = (*it).second;
      if ((it2 != d_defValues.end() && (defValue != (*it2).second)) ||
          (mayRepA.isConst() && mayRepB.isConst() && mayRepA != mayRepB)) {
        throw LogicException("Array theory solver does not yet support write-chains connecting two different constant arrays");
      }
    }
    else if (it2 != d_defValues.end()) {
      defValue = (*it2).second;
    }
    d_mayEqualEqualityEngine.assertEquality(a.eqNode(b), true, d_true);
    Assert(d_mayEqualEqualityEngine.consistent());
    if (!defValue.isNull()) {
      mayRepA = d_mayEqualEqualityEngine.getRepresentative(a);
      d_defValues[mayRepA] = defValue;
    }

    checkRowLemmas(a,b);
    checkRowLemmas(b,a);

    // merge info adds the list of the 2nd argument to the first
    d_infoMap.mergeInfo(a, b);

    if (options::arraysWeakEquivalence()) {
      d_arrayMerges.push_back(a.eqNode(b));
    }

    // If no more to do, break
    if (d_conflict || d_mergeQueue.empty()) {
      break;
    }

    // Otherwise, prepare for next iteration
    n = d_mergeQueue.front();
    a = n[0];
    b = n[1];
    d_mergeQueue.pop();
  }
  d_mergeInProgress = false;
}


void TheoryArrays::checkStore(TNode a) {
  if (options::arraysWeakEquivalence()) return;
  Trace("arrays-cri")<<"Arrays::checkStore "<<a<<"\n";

  if(Trace.isOn("arrays-cri")) {
    d_infoMap.getInfo(a)->print();
  }
  Assert(a.getType().isArray());
  Assert(a.getKind() == kind::STORE);
  TNode b = a[0];
  TNode i = a[1];

  TNode brep = d_equalityEngine->getRepresentative(b);

  if (!options::arraysOptimizeLinear() || d_infoMap.isNonLinear(brep)) {
    const CTNodeList* js = d_infoMap.getIndices(brep);
    size_t it = 0;
    RowLemmaType lem;
    for(; it < js->size(); ++it) {
      TNode j = (*js)[it];
      if (i == j) continue;
      lem = std::make_tuple(a, b, i, j);
      Trace("arrays-lem") << spaces(getSatContext()->getLevel()) <<"Arrays::checkStore ("<<a<<", "<<b<<", "<<i<<", "<<j<<")\n";
      queueRowLemma(lem);
    }
  }
}


void TheoryArrays::checkRowForIndex(TNode i, TNode a)
{
  if (options::arraysWeakEquivalence()) return;
  Trace("arrays-cri")<<"Arrays::checkRowForIndex "<<a<<"\n";
  Trace("arrays-cri")<<"                   index "<<i<<"\n";

  if(Trace.isOn("arrays-cri")) {
    d_infoMap.getInfo(a)->print();
  }
  Assert(a.getType().isArray());
  Assert(d_equalityEngine->getRepresentative(a) == a);

  TNode constArr = d_infoMap.getConstArr(a);
  if (!constArr.isNull()) {
    ArrayStoreAll storeAll = constArr.getConst<ArrayStoreAll>();
    Node defValue = storeAll.getValue();
    Node selConst = NodeManager::currentNM()->mkNode(kind::SELECT, constArr, i);
    if (!d_equalityEngine->hasTerm(selConst))
    {
      preRegisterTermInternal(selConst);
    }
    d_equalityEngine->assertEquality(selConst.eqNode(defValue), true, d_true);
  }

  const CTNodeList* stores = d_infoMap.getStores(a);
  const CTNodeList* instores = d_infoMap.getInStores(a);
  size_t it = 0;
  RowLemmaType lem;

  for(; it < stores->size(); ++it) {
    TNode store = (*stores)[it];
    Assert(store.getKind() == kind::STORE);
    TNode j = store[1];
    if (i == j) continue;
    lem = std::make_tuple(store, store[0], j, i);
    Trace("arrays-lem") << spaces(getSatContext()->getLevel()) <<"Arrays::checkRowForIndex ("<<store<<", "<<store[0]<<", "<<j<<", "<<i<<")\n";
    queueRowLemma(lem);
  }

  if (!options::arraysOptimizeLinear() || d_infoMap.isNonLinear(a)) {
    it = 0;
    for(; it < instores->size(); ++it) {
      TNode instore = (*instores)[it];
      Assert(instore.getKind() == kind::STORE);
      TNode j = instore[1];
      if (i == j) continue;
      lem = std::make_tuple(instore, instore[0], j, i);
      Trace("arrays-lem") << spaces(getSatContext()->getLevel()) <<"Arrays::checkRowForIndex ("<<instore<<", "<<instore[0]<<", "<<j<<", "<<i<<")\n";
      queueRowLemma(lem);
    }
  }
}


// a just became equal to b
// look for new ROW lemmas
void TheoryArrays::checkRowLemmas(TNode a, TNode b)
{
  if (options::arraysWeakEquivalence()) return;
  Trace("arrays-crl")<<"Arrays::checkLemmas begin \n"<<a<<"\n";
  if(Trace.isOn("arrays-crl"))
    d_infoMap.getInfo(a)->print();
  Trace("arrays-crl")<<"  ------------  and "<<b<<"\n";
  if(Trace.isOn("arrays-crl"))
    d_infoMap.getInfo(b)->print();

  const CTNodeList* i_a = d_infoMap.getIndices(a);
  size_t it = 0;
  TNode constArr = d_infoMap.getConstArr(b);
  if (!constArr.isNull()) {
    for( ; it < i_a->size(); ++it) {
      TNode i = (*i_a)[it];
      Node selConst = NodeManager::currentNM()->mkNode(kind::SELECT, constArr, i);
      if (!d_equalityEngine->hasTerm(selConst))
      {
        preRegisterTermInternal(selConst);
      }
    }
  }

  const CTNodeList* st_b = d_infoMap.getStores(b);
  const CTNodeList* inst_b = d_infoMap.getInStores(b);
  size_t its;

  RowLemmaType lem;

  for(it = 0 ; it < i_a->size(); ++it) {
    TNode i = (*i_a)[it];
    its = 0;
    for ( ; its < st_b->size(); ++its) {
      TNode store = (*st_b)[its];
      Assert(store.getKind() == kind::STORE);
      TNode j = store[1];
      TNode c = store[0];
      lem = std::make_tuple(store, c, j, i);
      Trace("arrays-lem") << spaces(getSatContext()->getLevel()) <<"Arrays::checkRowLemmas ("<<store<<", "<<c<<", "<<j<<", "<<i<<")\n";
      queueRowLemma(lem);
    }
  }

  if (!options::arraysOptimizeLinear() || d_infoMap.isNonLinear(b)) {
    for(it = 0 ; it < i_a->size(); ++it ) {
      TNode i = (*i_a)[it];
      its = 0;
      for ( ; its < inst_b->size(); ++its) {
        TNode store = (*inst_b)[its];
        Assert(store.getKind() == kind::STORE);
        TNode j = store[1];
        TNode c = store[0];
        lem = std::make_tuple(store, c, j, i);
        Trace("arrays-lem") << spaces(getSatContext()->getLevel()) <<"Arrays::checkRowLemmas ("<<store<<", "<<c<<", "<<j<<", "<<i<<")\n";
        queueRowLemma(lem);
      }
    }
  }
  Trace("arrays-crl")<<"Arrays::checkLemmas done.\n";
}

void TheoryArrays::propagate(RowLemmaType lem)
{
  Debug("pf::array") << "TheoryArrays: RowLemma Propagate called. options::arraysPropagate() = "
                     << options::arraysPropagate() << std::endl;

  TNode a, b, i, j;
  std::tie(a, b, i, j) = lem;

  Assert(a.getType().isArray() && b.getType().isArray());
  if (d_equalityEngine->areEqual(a, b) || d_equalityEngine->areEqual(i, j))
  {
    return;
  }

  NodeManager* nm = NodeManager::currentNM();
  Node aj = nm->mkNode(kind::SELECT, a, j);
  Node bj = nm->mkNode(kind::SELECT, b, j);

  // Try to avoid introducing new read terms: track whether these already exist
  bool ajExists = d_equalityEngine->hasTerm(aj);
  bool bjExists = d_equalityEngine->hasTerm(bj);
  bool bothExist = ajExists && bjExists;

  // If propagating, check propagations
  int prop = options::arraysPropagate();
  if (prop > 0) {
    if (d_equalityEngine->areDisequal(i, j, true) && (bothExist || prop > 1))
    {
      Trace("arrays-lem") << spaces(getSatContext()->getLevel()) <<"Arrays::queueRowLemma: propagating aj = bj ("<<aj<<", "<<bj<<")\n";
      Node aj_eq_bj = aj.eqNode(bj);
      Node reason =
          (i.isConst() && j.isConst()) ? d_true : i.eqNode(j).notNode();
      d_permRef.push_back(reason);
      if (!ajExists) {
        preRegisterTermInternal(aj);
      }
      if (!bjExists) {
        preRegisterTermInternal(bj);
      }
      d_equalityEngine->assertEquality(aj_eq_bj, true, reason, d_reasonRow);
      ++d_numProp;
      return;
    }
    if (bothExist && d_equalityEngine->areDisequal(aj, bj, true))
    {
      Trace("arrays-lem") << spaces(getSatContext()->getLevel()) <<"Arrays::queueRowLemma: propagating i = j ("<<i<<", "<<j<<")\n";
      Node reason =
          (aj.isConst() && bj.isConst()) ? d_true : aj.eqNode(bj).notNode();
      Node i_eq_j = i.eqNode(j);
      d_permRef.push_back(reason);
      d_equalityEngine->assertEquality(i_eq_j, true, reason, d_reasonRow);
      ++d_numProp;
      return;
    }
  }
}

void TheoryArrays::queueRowLemma(RowLemmaType lem)
{
  Debug("pf::array") << "Array solver: queue row lemma called" << std::endl;

  if (d_conflict || d_RowAlreadyAdded.contains(lem)) {
    return;
  }
  TNode a, b, i, j;
  std::tie(a, b, i, j) = lem;

  Assert(a.getType().isArray() && b.getType().isArray());
  if (d_equalityEngine->areEqual(a, b) || d_equalityEngine->areEqual(i, j))
  {
    return;
  }

  NodeManager* nm = NodeManager::currentNM();
  Node aj = nm->mkNode(kind::SELECT, a, j);
  Node bj = nm->mkNode(kind::SELECT, b, j);

  // Try to avoid introducing new read terms: track whether these already exist
  bool ajExists = d_equalityEngine->hasTerm(aj);
  bool bjExists = d_equalityEngine->hasTerm(bj);
  bool bothExist = ajExists && bjExists;

  // If propagating, check propagations
  int prop = options::arraysPropagate();
  if (prop > 0) {
    propagate(lem);
  }

  // If equivalent lemma already exists, don't enqueue this one
  if (d_useArrTable) {
    Node tableEntry = NodeManager::currentNM()->mkNode(kind::ARR_TABLE_FUN, a, b, i, j);
    if (d_equalityEngine->getSize(tableEntry) != 1)
    {
      return;
    }
  }

  // Prefer equality between indexes so as not to introduce new read terms
  if (options::arraysEagerIndexSplitting() && !bothExist
      && !d_equalityEngine->areDisequal(i, j, false))
  {
    Node i_eq_j;
    if (!d_proofsEnabled) {
      i_eq_j = d_valuation.ensureLiteral(i.eqNode(j)); // TODO: think about this
    } else {
      i_eq_j = i.eqNode(j);
    }

    getOutputChannel().requirePhase(i_eq_j, true);
    d_decisionRequests.push(i_eq_j);
  }

  // TODO: maybe add triggers here

  if ((options::arraysEagerLemmas() || bothExist) && !d_proofsEnabled) {
    // Make sure that any terms introduced by rewriting are appropriately stored in the equality database
    Node aj2 = Rewriter::rewrite(aj);
    if (aj != aj2) {
      if (!ajExists) {
        preRegisterTermInternal(aj);
      }
      if (!d_equalityEngine->hasTerm(aj2))
      {
        preRegisterTermInternal(aj2);
      }
      d_equalityEngine->assertEquality(aj.eqNode(aj2), true, d_true);
    }
    Node bj2 = Rewriter::rewrite(bj);
    if (bj != bj2) {
      if (!bjExists) {
        preRegisterTermInternal(bj);
      }
      if (!d_equalityEngine->hasTerm(bj2))
      {
        preRegisterTermInternal(bj2);
      }
      d_equalityEngine->assertEquality(bj.eqNode(bj2), true, d_true);
    }
    if (aj2 == bj2) {
      return;
    }

    // construct lemma
    Node eq1 = aj2.eqNode(bj2);
    Node eq1_r = Rewriter::rewrite(eq1);
    if (eq1_r == d_true) {
      if (!d_equalityEngine->hasTerm(aj2))
      {
        preRegisterTermInternal(aj2);
      }
      if (!d_equalityEngine->hasTerm(bj2))
      {
        preRegisterTermInternal(bj2);
      }
      d_equalityEngine->assertEquality(eq1, true, d_true);
      return;
    }

    Node eq2 = i.eqNode(j);
    Node eq2_r = Rewriter::rewrite(eq2);
    if (eq2_r == d_true) {
      d_equalityEngine->assertEquality(eq2, true, d_true);
      return;
    }

    Node lemma = nm->mkNode(kind::OR, eq2_r, eq1_r);

    Trace("arrays-lem")<<"Arrays::addRowLemma adding "<<lemma<<"\n";
    d_RowAlreadyAdded.insert(lem);
    d_out->lemma(lemma);
    ++d_numRow;
  }
  else {
    d_RowQueue.push(lem);
  }
}

Node TheoryArrays::getNextDecisionRequest()
{
  if(! d_decisionRequests.empty()) {
    Node n = d_decisionRequests.front();
    d_decisionRequests.pop();
    return n;
  }
  return Node::null();
}


bool TheoryArrays::dischargeLemmas()
{
  bool lemmasAdded = false;
  size_t sz = d_RowQueue.size();
  for (unsigned count = 0; count < sz; ++count) {
    RowLemmaType l = d_RowQueue.front();
    d_RowQueue.pop();
    if (d_RowAlreadyAdded.contains(l)) {
      continue;
    }

    TNode a, b, i, j;
    std::tie(a, b, i, j) = l;
    Assert(a.getType().isArray() && b.getType().isArray());

    NodeManager* nm = NodeManager::currentNM();
    Node aj = nm->mkNode(kind::SELECT, a, j);
    Node bj = nm->mkNode(kind::SELECT, b, j);
    bool ajExists = d_equalityEngine->hasTerm(aj);
    bool bjExists = d_equalityEngine->hasTerm(bj);

    // Check for redundant lemma
    // TODO: more checks possible (i.e. check d_RowAlreadyAdded in context)
    if (!d_equalityEngine->hasTerm(i) || !d_equalityEngine->hasTerm(j)
        || d_equalityEngine->areEqual(i, j) || !d_equalityEngine->hasTerm(a)
        || !d_equalityEngine->hasTerm(b) || d_equalityEngine->areEqual(a, b)
        || (ajExists && bjExists && d_equalityEngine->areEqual(aj, bj)))
    {
      continue;
    }

    int prop = options::arraysPropagate();
    if (prop > 0) {
      propagate(l);
      if (d_conflict) {
        return true;
      }
    }

    // Make sure that any terms introduced by rewriting are appropriately stored in the equality database
    Node aj2 = Rewriter::rewrite(aj);
    if (aj != aj2) {
      if (!ajExists) {
        preRegisterTermInternal(aj);
      }
      if (!d_equalityEngine->hasTerm(aj2))
      {
        preRegisterTermInternal(aj2);
      }
      d_equalityEngine->assertEquality(aj.eqNode(aj2), true, d_true);
    }
    Node bj2 = Rewriter::rewrite(bj);
    if (bj != bj2) {
      if (!bjExists) {
        preRegisterTermInternal(bj);
      }
      if (!d_equalityEngine->hasTerm(bj2))
      {
        preRegisterTermInternal(bj2);
      }
      d_equalityEngine->assertEquality(bj.eqNode(bj2), true, d_true);
    }
    if (aj2 == bj2) {
      continue;
    }

    // construct lemma
    Node eq1 = aj2.eqNode(bj2);
    Node eq1_r = Rewriter::rewrite(eq1);
    if (eq1_r == d_true) {
      if (!d_equalityEngine->hasTerm(aj2))
      {
        preRegisterTermInternal(aj2);
      }
      if (!d_equalityEngine->hasTerm(bj2))
      {
        preRegisterTermInternal(bj2);
      }
      d_equalityEngine->assertEquality(eq1, true, d_true);
      continue;
    }

    Node eq2 = i.eqNode(j);
    Node eq2_r = Rewriter::rewrite(eq2);
    if (eq2_r == d_true) {
      d_equalityEngine->assertEquality(eq2, true, d_true);
      continue;
    }

    Node lem = nm->mkNode(kind::OR, eq2_r, eq1_r);

    Trace("arrays-lem")<<"Arrays::addRowLemma adding "<<lem<<"\n";
    d_RowAlreadyAdded.insert(l);
    d_out->lemma(lem);
    ++d_numRow;
    lemmasAdded = true;
    if (options::arraysReduceSharing()) {
      return true;
    }
  }
  return lemmasAdded;
}

void TheoryArrays::conflict(TNode a, TNode b) {
  Debug("pf::array") << "TheoryArrays::Conflict called" << std::endl;
  std::shared_ptr<eq::EqProof> proof = d_proofsEnabled ?
      std::make_shared<eq::EqProof>() : nullptr;

  d_conflictNode = explain(a.eqNode(b), proof.get());

  if (!d_inCheckModel) {
    std::unique_ptr<ProofArray> proof_array;

    if (d_proofsEnabled) {
      proof->debug_print("pf::array");
      proof_array.reset(new ProofArray(proof,
                                       /*row=*/d_reasonRow,
                                       /*row1=*/d_reasonRow1,
                                       /*ext=*/d_reasonExt));
    }

    d_out->conflict(d_conflictNode, std::move(proof_array));
  }

  d_conflict = true;
}

TheoryArrays::TheoryArraysDecisionStrategy::TheoryArraysDecisionStrategy(
    TheoryArrays* ta)
    : d_ta(ta)
{
}
void TheoryArrays::TheoryArraysDecisionStrategy::initialize() {}
Node TheoryArrays::TheoryArraysDecisionStrategy::getNextDecisionRequest()
{
  return d_ta->getNextDecisionRequest();
}
std::string TheoryArrays::TheoryArraysDecisionStrategy::identify() const
{
  return std::string("th_arrays_dec");
}

TrustNode TheoryArrays::expandDefinition(Node node)
{
  NodeManager* nm = NodeManager::currentNM();
  Kind kind = node.getKind();

  /* Expand
   *
   *   (eqrange a b i j)
   *
   * to
   *
   *  forall k . i <= k <= j => a[k] = b[k]
   *
   */
  if (kind == kind::EQ_RANGE)
  {
    TNode a = node[0];
    TNode b = node[1];
    TNode i = node[2];
    TNode j = node[3];
    Node k = nm->mkBoundVar(i.getType());
    Node bvl = nm->mkNode(kind::BOUND_VAR_LIST, k);
    TypeNode type = k.getType();

    Kind kle;
    Node range;
    if (type.isBitVector())
    {
      kle = kind::BITVECTOR_ULE;
    }
    else if (type.isFloatingPoint())
    {
      kle = kind::FLOATINGPOINT_LEQ;
    }
    else if (type.isInteger() || type.isReal())
    {
      kle = kind::LEQ;
    }
    else
    {
      Unimplemented() << "Type " << type << " is not supported for predicate "
                      << kind;
    }

    range = nm->mkNode(kind::AND, nm->mkNode(kle, i, k), nm->mkNode(kle, k, j));

    Node eq = nm->mkNode(kind::EQUAL,
                         nm->mkNode(kind::SELECT, a, k),
                         nm->mkNode(kind::SELECT, b, k));
    Node implies = nm->mkNode(kind::IMPLIES, range, eq);
    Node ret = nm->mkNode(kind::FORALL, bvl, implies);
    return TrustNode::mkTrustRewrite(node, ret, nullptr);
  }
  return TrustNode::null();
}

void TheoryArrays::computeRelevantTerms(std::set<Node>& termSet,
                                        bool includeShared)
{
  // include all standard terms
  std::set<Kind> irrKinds;
  computeRelevantTermsInternal(termSet, irrKinds, includeShared);

  NodeManager* nm = NodeManager::currentNM();
  // make sure RIntro1 reads are included in the relevant set of reads
  eq::EqClassesIterator eqcs_i = eq::EqClassesIterator(d_equalityEngine);
  for (; !eqcs_i.isFinished(); ++eqcs_i)
  {
    Node eqc = (*eqcs_i);
    if (!eqc.getType().isArray())
    {
      // not an array, skip
      continue;
    }
    eq::EqClassIterator eqc_i = eq::EqClassIterator(eqc, d_equalityEngine);
    for (; !eqc_i.isFinished(); ++eqc_i)
    {
      Node n = *eqc_i;
      if (termSet.find(n) != termSet.end())
      {
        if (n.getKind() == kind::STORE)
        {
          // Make sure RIntro1 reads are included
          Node r = nm->mkNode(kind::SELECT, n, n[1]);
          Trace("arrays::collectModelInfo")
              << "TheoryArrays::collectModelInfo, adding RIntro1 read: " << r
              << endl;
          termSet.insert(r);
        }
      }
    }
  }

  // Now do a fixed-point iteration to get all reads that need to be included
  // because of RIntro2 rule
  bool changed;
  do
  {
    changed = false;
    eqcs_i = eq::EqClassesIterator(d_equalityEngine);
    for (; !eqcs_i.isFinished(); ++eqcs_i)
    {
      Node eqc = (*eqcs_i);
      eq::EqClassIterator eqc_i = eq::EqClassIterator(eqc, d_equalityEngine);
      for (; !eqc_i.isFinished(); ++eqc_i)
      {
        Node n = *eqc_i;
        if (n.getKind() == kind::SELECT && termSet.find(n) != termSet.end())
        {
          // Find all terms equivalent to n[0] and get corresponding read terms
          Node array_eqc = d_equalityEngine->getRepresentative(n[0]);
          eq::EqClassIterator array_eqc_i =
              eq::EqClassIterator(array_eqc, d_equalityEngine);
          for (; !array_eqc_i.isFinished(); ++array_eqc_i)
          {
            Node arr = *array_eqc_i;
            if (arr.getKind() == kind::STORE
                && termSet.find(arr) != termSet.end()
                && !d_equalityEngine->areEqual(arr[1], n[1]))
            {
              Node r = nm->mkNode(kind::SELECT, arr, n[1]);
              if (termSet.find(r) == termSet.end()
                  && d_equalityEngine->hasTerm(r))
              {
                Trace("arrays::collectModelInfo")
                    << "TheoryArrays::collectModelInfo, adding RIntro2(a) "
                       "read: "
                    << r << endl;
                termSet.insert(r);
                changed = true;
              }
              r = nm->mkNode(kind::SELECT, arr[0], n[1]);
              if (termSet.find(r) == termSet.end()
                  && d_equalityEngine->hasTerm(r))
              {
                Trace("arrays::collectModelInfo")
                    << "TheoryArrays::collectModelInfo, adding RIntro2(b) "
                       "read: "
                    << r << endl;
                termSet.insert(r);
                changed = true;
              }
            }
          }

          // Find all stores in which n[0] appears and get corresponding read
          // terms
          const CTNodeList* instores = d_infoMap.getInStores(array_eqc);
          size_t it = 0;
          for (; it < instores->size(); ++it)
          {
            TNode instore = (*instores)[it];
            Assert(instore.getKind() == kind::STORE);
            if (termSet.find(instore) != termSet.end()
                && !d_equalityEngine->areEqual(instore[1], n[1]))
            {
              Node r = nm->mkNode(kind::SELECT, instore, n[1]);
              if (termSet.find(r) == termSet.end()
                  && d_equalityEngine->hasTerm(r))
              {
                Trace("arrays::collectModelInfo")
                    << "TheoryArrays::collectModelInfo, adding RIntro2(c) "
                       "read: "
                    << r << endl;
                termSet.insert(r);
                changed = true;
              }
              r = nm->mkNode(kind::SELECT, instore[0], n[1]);
              if (termSet.find(r) == termSet.end()
                  && d_equalityEngine->hasTerm(r))
              {
                Trace("arrays::collectModelInfo")
                    << "TheoryArrays::collectModelInfo, adding RIntro2(d) "
                       "read: "
                    << r << endl;
                termSet.insert(r);
                changed = true;
              }
            }
          }
        }
      }
    }
  } while (changed);
}

}/* CVC4::theory::arrays namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */
