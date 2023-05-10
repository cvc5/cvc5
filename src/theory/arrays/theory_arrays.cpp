/******************************************************************************
 * Top contributors (to current version):
 *   Clark Barrett, Andrew Reynolds, Morgan Deters
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Implementation of the theory of arrays.
 */

#include "theory/arrays/theory_arrays.h"

#include <map>
#include <memory>

#include "expr/array_store_all.h"
#include "expr/kind.h"
#include "expr/node_algorithm.h"
#include "options/arrays_options.h"
#include "options/smt_options.h"
#include "proof/proof_checker.h"
#include "smt/logic_exception.h"
#include "theory/arrays/skolem_cache.h"
#include "theory/arrays/theory_arrays_rewriter.h"
#include "theory/decision_manager.h"
#include "theory/theory_model.h"
#include "theory/trust_substitutions.h"
#include "theory/valuation.h"

using namespace std;

namespace cvc5::internal {
namespace theory {
namespace arrays {

// These are the options that produce the best empirical results on QF_AX benchmarks.
// eagerLemmas = true
// eagerIndexSplitting = false

// Use static configuration of options for now
const bool d_ccStore = false;
  //const bool d_eagerLemmas = false;
const bool d_preprocess = true;
const bool d_solveWrite = true;
const bool d_solveWrite2 = false;
  // These are now options
  //const bool d_propagateLemmas = true;
  //bool d_useNonLinearOpt = true;
  //bool d_eagerIndexSplitting = false;

TheoryArrays::TheoryArrays(Env& env,
                           OutputChannel& out,
                           Valuation valuation,
                           std::string name)
    : Theory(THEORY_ARRAYS, env, out, valuation, name),
      d_numRow(statisticsRegistry().registerInt(name + "number of Row lemmas")),
      d_numExt(statisticsRegistry().registerInt(name + "number of Ext lemmas")),
      d_numProp(
          statisticsRegistry().registerInt(name + "number of propagations")),
      d_numExplain(
          statisticsRegistry().registerInt(name + "number of explanations")),
      d_numNonLinear(statisticsRegistry().registerInt(
          name + "number of calls to setNonLinear")),
      d_numSharedArrayVarSplits(statisticsRegistry().registerInt(
          name + "number of shared array var splits")),
      d_numGetModelValSplits(statisticsRegistry().registerInt(
          name + "number of getModelVal splits")),
      d_numGetModelValConflicts(statisticsRegistry().registerInt(
          name + "number of getModelVal conflicts")),
      d_numSetModelValSplits(statisticsRegistry().registerInt(
          name + "number of setModelVal splits")),
      d_numSetModelValConflicts(statisticsRegistry().registerInt(
          name + "number of setModelVal conflicts")),
      d_ppEqualityEngine(d_env, userContext(), name + "pp", true),
      d_ppFacts(userContext()),
      d_rewriter(env),
      d_state(env, valuation),
      d_im(env, *this, d_state),
      d_literalsToPropagate(context()),
      d_literalsToPropagateIndex(context(), 0),
      d_isPreRegistered(context()),
      d_mayEqualEqualityEngine(d_env, context(), name + "mayEqual", true),
      d_notify(*this),
      d_infoMap(statisticsRegistry(), context(), name),
      d_mergeQueue(context()),
      d_mergeInProgress(false),
      d_RowQueue(context()),
      d_RowAlreadyAdded(userContext()),
      d_sharedArrays(context()),
      d_sharedOther(context()),
      d_sharedTerms(context(), false),
      d_reads(context()),
      d_constReadsList(context()),
      d_constReadsContext(new context::Context()),
      d_contextPopper(context(), d_constReadsContext),
      d_decisionRequests(context()),
      d_permRef(context()),
      d_modelConstraints(context()),
      d_lemmasSaved(context()),
      d_defValues(context()),
      d_readTableContext(new context::Context()),
      d_arrayMerges(context()),
      d_dstrat(new TheoryArraysDecisionStrategy(this)),
      d_dstratInit(false)
{
  d_true = NodeManager::currentNM()->mkConst<bool>(true);
  d_false = NodeManager::currentNM()->mkConst<bool>(false);

  // The preprocessing congruence kinds
  d_ppEqualityEngine.addFunctionKind(kind::SELECT);
  d_ppEqualityEngine.addFunctionKind(kind::STORE);

  // indicate we are using the default theory state object, and the arrays
  // inference manager
  d_theoryState = &d_state;
  d_inferManager = &d_im;
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
}

TheoryRewriter* TheoryArrays::getTheoryRewriter() { return &d_rewriter; }

ProofRuleChecker* TheoryArrays::getProofChecker() { return &d_checker; }

bool TheoryArrays::needsEqualityEngine(EeSetupInfo& esi)
{
  esi.d_notify = &d_notify;
  esi.d_name = d_instanceName + "ee";
  esi.d_notifyNewClass = true;
  esi.d_notifyMerge = true;
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
}

/////////////////////////////////////////////////////////////////////////////
// PREPROCESSING
/////////////////////////////////////////////////////////////////////////////


bool TheoryArrays::ppDisequal(TNode a, TNode b) {
  bool termsExist = d_ppEqualityEngine.hasTerm(a) && d_ppEqualityEngine.hasTerm(b);
  Assert(!termsExist || !a.isConst() || !b.isConst() || a == b
         || d_ppEqualityEngine.areDisequal(a, b, false));
  return ((termsExist && d_ppEqualityEngine.areDisequal(a, b, false))
          || rewrite(a.eqNode(b)) == d_false);
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
    NodeBuilder result(kind::AND);
    int i, j;
    write_i = left;
    for (i = leftWrites-1; i >= 0; --i) {
      index_i = write_i[1];

      // build: [index_i /= index_n && index_i /= index_(n-1) &&
      //         ... && index_i /= index_(i+1)] -> read(store, index_i) = v_i
      write_j = left;
      {
        NodeBuilder hyp(kind::AND);
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
    NodeBuilder nb(kind::AND);
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

TrustNode TheoryArrays::ppRewrite(TNode term, std::vector<SkolemLemma>& lems)
{
  // first, check for logic exceptions
  Kind k = term.getKind();
  if (!options().arrays.arraysExp)
  {
    if (k == kind::EQ_RANGE)
    {
      std::stringstream ss;
      ss << "Term of kind `" << k
         << "` not supported in default mode, try `--arrays-exp`.";
      throw LogicException(ss.str());
    }
  }
  // see if we need to expand definitions
  TrustNode texp = d_rewriter.expandDefinition(term);
  if (!texp.isNull())
  {
    return texp;
  }
  if (!d_preprocess)
  {
    return TrustNode::null();
  }
  d_ppEqualityEngine.addTerm(term);
  NodeManager* nm = NodeManager::currentNM();
  Node ret;
  switch (k)
  {
    case kind::SELECT: {
      // select(store(a,i,v),j) = select(a,j)
      //    IF i != j
      if (term[0].getKind() == kind::STORE && ppDisequal(term[0][1], term[1])) {
        ret = nm->mkNode(kind::SELECT, term[0][0], term[1]);
      }
      break;
    }
    case kind::STORE: {
      // store(store(a,i,v),j,w) = store(store(a,j,w),i,v)
      //    IF i != j and j comes before i in the ordering
      if (term[0].getKind() == kind::STORE && (term[1] < term[0][1]) && ppDisequal(term[1],term[0][1])) {
        Node inner = nm->mkNode(kind::STORE, term[0][0], term[1], term[2]);
        Node outer = nm->mkNode(kind::STORE, inner, term[0][1], term[0][2]);
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

Theory::PPAssertStatus TheoryArrays::ppAssert(
    TrustNode tin, TrustSubstitutionMap& outSubstitutions)
{
  TNode in = tin.getNode();
  switch(in.getKind()) {
    case kind::EQUAL:
    {
      d_ppFacts.push_back(in);
      d_ppEqualityEngine.assertEquality(in, true, in);
      if (in[0].isVar() && isLegalElimination(in[0], in[1]))
      {
        outSubstitutions.addSubstitutionSolved(in[0], in[1], tin);
        return PP_ASSERT_STATUS_SOLVED;
      }
      if (in[1].isVar() && isLegalElimination(in[1], in[0]))
      {
        outSubstitutions.addSubstitutionSolved(in[1], in[0], tin);
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

bool TheoryArrays::propagateLit(TNode literal)
{
  Trace("arrays") << spaces(context()->getLevel())
                  << "TheoryArrays::propagateLit(" << literal << ")"
                  << std::endl;

  // If already in conflict, no more propagation
  if (d_state.isInConflict())
  {
    Trace("arrays") << spaces(context()->getLevel())
                    << "TheoryArrays::propagateLit(" << literal
                    << "): already in conflict" << std::endl;
    return false;
  }

  bool ok = d_out->propagate(literal);
  if (!ok) {
    d_state.notifyInConflict();
  }
  return ok;
}/* TheoryArrays::propagate(TNode) */


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
  std::unordered_set<TNode> marked;
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
  if (d_state.isInConflict())
  {
    return;
  }
  Trace("arrays") << spaces(context()->getLevel())
                  << "TheoryArrays::preRegisterTerm(" << node << ")"
                  << std::endl;
  Kind nk = node.getKind();
  if (nk == kind::EQUAL)
  {
    // Add the trigger for equality
    // NOTE: note that if the equality is true or false already, it might not be added
    d_state.addEqualityEngineTriggerPredicate(node);
    return;
  }
  // add to equality engine and the may equality engine
  TypeNode nodeType = node.getType();
  if (nodeType.isArray())
  {
    // index type should not be an array, otherwise we throw a logic exception
    if (nodeType.getArrayIndexType().isArray())
    {
      std::stringstream ss;
      ss << "Arrays cannot be indexed by array types, offending array type is "
         << nodeType;
      throw LogicException(ss.str());
    }
    d_mayEqualEqualityEngine.addTerm(node);
  }
  if (d_equalityEngine->hasTerm(node))
  {
    // Notice that array terms may be added to its equality engine before
    // being preregistered in the central equality engine architecture.
    // Prior to this, an assertion in this case was:
    // Assert(nk != kind::SELECT
    //         || d_isPreRegistered.find(node) != d_isPreRegistered.end());
    return;
  }
  d_equalityEngine->addTerm(node);

  switch (node.getKind())
  {
    case kind::SELECT:
    {
      // Reads
      TNode store = d_equalityEngine->getRepresentative(node[0]);

      // The may equal needs the store
      d_mayEqualEqualityEngine.addTerm(store);

      Assert((d_isPreRegistered.insert(node), true));

      Assert(d_equalityEngine->getRepresentative(store) == store);
      d_infoMap.addIndex(store, node[1]);

      // Synchronize d_constReadsContext with SAT context
      Assert(d_constReadsContext->getLevel() <= context()->getLevel());
      while (d_constReadsContext->getLevel() < context()->getLevel())
      {
        d_constReadsContext->push();
      }

      // Record read in sharing data structure
      TNode index = d_equalityEngine->getRepresentative(node[1]);
      if (!options().arrays.arraysWeakEquivalence && index.isConst())
      {
        CTNodeList* temp;
        CNodeNListMap::iterator it = d_constReads.find(index);
        if (it == d_constReads.end())
        {
          temp = new (true) CTNodeList(d_constReadsContext);
          d_constReads[index] = temp;
        }
        else
        {
          temp = (*it).second;
        }
        temp->push_back(node);
        d_constReadsList.push_back(node);
      }
      else
      {
        d_reads.push_back(node);
      }

      checkRowForIndex(node[1], store);
      break;
    }
    case kind::STORE:
    {
      TNode a = d_equalityEngine->getRepresentative(node[0]);

      if (node.isConst())
      {
        // Can't use d_mayEqualEqualityEngine to merge node with a because they
        // are both constants, so just set the default value manually for node.
        Assert(a == node[0]);
        d_mayEqualEqualityEngine.addTerm(node);
        Assert(d_mayEqualEqualityEngine.getRepresentative(node) == node);
        Assert(d_mayEqualEqualityEngine.getRepresentative(a) == a);
        DefValMap::iterator it = d_defValues.find(a);
        Assert(it != d_defValues.end());
        d_defValues[node] = (*it).second;
      }
      else
      {
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
      d_im.assertInference(ni.eqNode(v),
                           true,
                           InferenceId::ARRAYS_READ_OVER_WRITE_1,
                           d_true,
                           PfRule::ARRAYS_READ_OVER_WRITE_1);

      d_infoMap.addStore(node, node);
      d_infoMap.addInStore(a, node);
      d_infoMap.setModelRep(node, node);

      // Add-Store for Weak Equivalence
      if (options().arrays.arraysWeakEquivalence)
      {
        Assert(weakEquivGetRep(node[0]) == weakEquivGetRep(a));
        Assert(weakEquivGetRep(node) == node);
        d_infoMap.setWeakEquivPointer(node, node[0]);
        d_infoMap.setWeakEquivIndex(node, node[1]);
#ifdef CVC5_ASSERTIONS
        checkWeakEquiv(false);
#endif
    }

    checkStore(node);
    break;
  }
  case kind::STORE_ALL: {
    ArrayStoreAll storeAll = node.getConst<ArrayStoreAll>();
    Node defaultValue = storeAll.getValue();
    if (!defaultValue.isConst()) {
      throw LogicException("Array theory solver does not yet support non-constant default values for arrays");
    }
    d_infoMap.setConstArr(node, node);
    Assert(d_mayEqualEqualityEngine.getRepresentative(node) == node);
    d_defValues[node] = defaultValue;
    setNonLinear(node);
    break;
  }
  default:
    // Variables etc, already processed above
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
    d_state.addEqualityEngineTriggerPredicate(node);
  }
}

TrustNode TheoryArrays::explain(TNode literal)
{
  return d_im.explainLit(literal);
}

/////////////////////////////////////////////////////////////////////////////
// SHARING
/////////////////////////////////////////////////////////////////////////////

void TheoryArrays::notifySharedTerm(TNode t)
{
  Trace("arrays::sharing") << spaces(context()->getLevel())
                           << "TheoryArrays::notifySharedTerm(" << t << ")"
                           << std::endl;
  if (t.getType().isArray()) {
    d_sharedArrays.insert(t);
  }
  else {
#ifdef CVC5_ASSERTIONS
    d_sharedOther.insert(t);
#endif
    d_sharedTerms = true;
  }
}

void TheoryArrays::checkPair(TNode r1, TNode r2)
{
  Trace("arrays::sharing") << "TheoryArrays::computeCareGraph(): checking reads " << r1 << " and " << r2 << std::endl;

  TNode x = r1[1];
  TNode y = r2[1];
  Assert(d_equalityEngine->isTriggerTerm(x, THEORY_ARRAYS));

  if (d_equalityEngine->hasTerm(x) && d_equalityEngine->hasTerm(y)
      && (d_equalityEngine->areEqual(x, y)
          || d_equalityEngine->areDisequal(x, y, false)))
  {
    Trace("arrays::sharing") << "TheoryArrays::computeCareGraph(): equality known, skipping" << std::endl;
    return;
  }

  // If the terms are already known to be equal, we are also in good shape
  if (d_equalityEngine->areEqual(r1, r2))
  {
    Trace("arrays::sharing") << "TheoryArrays::computeCareGraph(): equal, skipping" << std::endl;
    return;
  }

  if (r1[0] != r2[0]) {
    // If arrays are known to be disequal, or cannot become equal, we can continue
    Assert(d_mayEqualEqualityEngine.hasTerm(r1[0])
           && d_mayEqualEqualityEngine.hasTerm(r2[0]));
    if (r1[0].getType() != r2[0].getType()
        || d_equalityEngine->areDisequal(r1[0], r2[0], false))
    {
      Trace("arrays::sharing") << "TheoryArrays::computeCareGraph(): arrays can't be equal, skipping" << std::endl;
      return;
    }
    else if (!d_mayEqualEqualityEngine.areEqual(r1[0], r2[0])) {
      return;
    }
  }

  if (!d_equalityEngine->isTriggerTerm(y, THEORY_ARRAYS))
  {
    Trace("arrays::sharing") << "TheoryArrays::computeCareGraph(): not connected to shared terms, skipping" << std::endl;
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
      Trace("arrays::sharing") << "TheoryArrays::computeCareGraph(): missed propagation" << std::endl;
      break;
    case EQUALITY_FALSE_AND_PROPAGATED:
      Trace("arrays::sharing") << "TheoryArrays::computeCareGraph(): checkPair "
                                  "called when false in model"
                               << std::endl;
      // Should have been propagated to us
      Assert(false);
      break;
    case EQUALITY_FALSE: CVC5_FALLTHROUGH;
    case EQUALITY_FALSE_IN_MODEL:
      // This is unlikely, but I think it could happen
      Trace("arrays::sharing") << "TheoryArrays::computeCareGraph(): checkPair called when false in model" << std::endl;
      return;
    default:
      // Covers EQUALITY_TRUE_IN_MODEL (common case) and EQUALITY_UNKNOWN
      break;
  }

  // Add this pair
  Trace("arrays::sharing") << "TheoryArrays::computeCareGraph(): adding to care-graph" << std::endl;
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
    Assert(d_constReadsContext->getLevel() <= context()->getLevel());
    while (d_constReadsContext->getLevel() < context()->getLevel())
    {
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

      Trace("arrays::sharing") << "TheoryArrays::computeCareGraph(): checking read " << r1 << std::endl;
      Assert(d_equalityEngine->hasTerm(r1));
      TNode x = r1[1];

      if (!d_equalityEngine->isTriggerTerm(x, THEORY_ARRAYS))
      {
        Trace("arrays::sharing") << "TheoryArrays::computeCareGraph(): not connected to shared terms, skipping" << std::endl;
        continue;
      }
      Node x_shared =
          d_equalityEngine->getTriggerTermRepresentative(x, THEORY_ARRAYS);

      // Get the model value of index and find all reads that read from that same model value: these are the pairs we have to check
      // Also, insert this read in the list at the proper index

      if (!x_shared.isConst()) {
        x_shared = d_valuation.getCandidateModelValue(x_shared);
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
        // We don't know the model value for x.  Just do brute force examination of all pairs of reads.
        // Note that we have to loop over *all* reads here, not just subsequent reads, because there
        // may be an earlier read that *does* have a model value.  So if we don't check here, the two
        // reads won't get compared.
        for (unsigned j = 0; j < size; ++j)
        {
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

bool TheoryArrays::collectModelValues(TheoryModel* m,
                                      const std::set<Node>& termSet)
{
  // termSet contains terms appearing in assertions and shared terms, and also
  // includes additional reads due to the RIntro1 and RIntro2 rules.
  NodeManager* nm = NodeManager::currentNM();
  // Compute arrays that we need to produce representatives for
  std::vector<Node> arrays;

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
      // If this EC is an array type and it contains something other than STORE
      // nodes, we have to compute a representative explicitly
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
  for (; set_it != set_it_end; ++set_it)
  {
    Node n = *set_it;
    // If this term is a select, record that the EC rep of its store parameter
    // is being read from using this term
    if (n.getKind() == kind::SELECT)
    {
      selects[d_equalityEngine->getRepresentative(n[0])].push_back(n);
    }
  }

  Node rep;
  DefValMap::iterator it;
  TypeSet defaultValuesSet;

  // Compute all default values already in use
  // if (fullModel) {
  for (size_t i = 0; i < arrays.size(); ++i)
  {
    TNode nrep = d_equalityEngine->getRepresentative(arrays[i]);
    d_mayEqualEqualityEngine.addTerm(
        nrep);  // add the term in case it isn't there already
    TNode mayRep = d_mayEqualEqualityEngine.getRepresentative(nrep);
    it = d_defValues.find(mayRep);
    if (it != d_defValues.end())
    {
      defaultValuesSet.add(nrep.getType().getArrayConstituentType(),
                           (*it).second);
    }
  }
  //}

  // Loop through all array equivalence classes that need a representative
  // computed
  for (size_t i = 0; i < arrays.size(); ++i)
  {
    TNode n = arrays[i];
    TNode nrep = d_equalityEngine->getRepresentative(n);

    // if (fullModel) {
    // Compute default value for this array - there is one default value for
    // every mayEqual equivalence class
    TNode mayRep = d_mayEqualEqualityEngine.getRepresentative(nrep);
    it = d_defValues.find(mayRep);
    // If this mayEqual EC doesn't have a default value associated, get the next
    // available default value for the associated array element type
    if (it == d_defValues.end())
    {
      TypeNode valueType = nrep.getType().getArrayConstituentType();
      rep = defaultValuesSet.nextTypeEnum(valueType);
      if (rep.isNull())
      {
        Assert(defaultValuesSet.getSet(valueType)->begin()
               != defaultValuesSet.getSet(valueType)->end());
        rep = *(defaultValuesSet.getSet(valueType)->begin());
      }
      Trace("arrays-models") << "New default value = " << rep << endl;
      d_defValues[mayRep] = rep;
    }
    else
    {
      rep = (*it).second;
    }

    // Build the STORE_ALL term with the default value
    rep = nm->mkConst(ArrayStoreAll(nrep.getType(), rep));

    // For each read, require that the rep stores the right value
    vector<Node>& reads = selects[nrep];
    for (unsigned j = 0; j < reads.size(); ++j)
    {
      rep = nm->mkNode(kind::STORE, rep, reads[j][1], reads[j]);
    }
    if (!m->assertEquality(n, rep, true))
    {
      return false;
    }
    if (!n.isConst())
    {
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
    d_im.getDecisionManager()->registerStrategy(
        DecisionManager::STRAT_ARRAYS,
        d_dstrat.get(),
        DecisionManager::STRAT_SCOPE_CTX_INDEPENDENT);
  }
}


/////////////////////////////////////////////////////////////////////////////
// MAIN SOLVER
/////////////////////////////////////////////////////////////////////////////

Node TheoryArrays::getSkolem(TNode ref)
{
  Node skolem = SkolemCache::getExtIndexSkolem(ref);

  Trace("pf::array") << "Pregistering a Skolem" << std::endl;
  preRegisterTermInternal(skolem);
  Trace("pf::array") << "Pregistering a Skolem DONE" << std::endl;

  Trace("pf::array") << "getSkolem DONE" << std::endl;
  return skolem;
}

void TheoryArrays::postCheck(Effort level)
{
  bool eagerLemmas = options().arrays.arraysEagerLemmas;
  bool weakEquiv = options().arrays.arraysWeakEquivalence;

  if ((eagerLemmas || fullEffort(level)) && !d_state.isInConflict()
      && weakEquiv)
  {
    // Replay all array merges to update weak equivalence data structures
    context::CDList<Node>::iterator it = d_arrayMerges.begin(),
                                    iend = d_arrayMerges.end();
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
#ifdef CVC5_ASSERTIONS
      checkWeakEquiv(false);
#endif
    }
#ifdef CVC5_ASSERTIONS
    checkWeakEquiv(true);
#endif

    d_readTableContext->push();
    TNode mayRep, iRep;
    CTNodeList* bucketList = NULL;
    CTNodeList::const_iterator i = d_reads.begin(), readsEnd = d_reads.end();
    for (; i != readsEnd; ++i) {
      const TNode& r = *i;

      Trace("arrays::weak") << "TheoryArrays::check(): checking read " << r << std::endl;

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
          Assert(d_equalityEngine->areEqual(r, rewrite(r)));
          Assert(d_equalityEngine->areEqual(r2, rewrite(r2)));
          Node lemma = rewrite(r).eqNode(rewrite(r2)).negate();
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
          Trace("arrays-lem")
              << "Arrays::addExtLemma (weak-eq) " << lemma << "\n";
          d_out->lemma(lemma, LemmaProperty::SEND_ATOMS);
          d_readTableContext->pop();
          Trace("arrays") << spaces(context()->getLevel())
                          << "Arrays::check(): done" << endl;
          return;
        }
      }
      bucketList->push_back(r);
    }
    d_readTableContext->pop();
  }

  if (!eagerLemmas && fullEffort(level) && !d_state.isInConflict()
      && !weakEquiv)
  {
    // generate the lemmas on the worklist
    Trace("arrays-lem")<< "Arrays::discharging lemmas. Number of queued lemmas: " << d_RowQueue.size() << "\n";
    while (d_RowQueue.size() > 0 && !d_state.isInConflict())
    {
      if (dischargeLemmas()) {
        break;
      }
    }
  }

  Trace("arrays") << spaces(context()->getLevel()) << "Arrays::check(): done"
                  << endl;
}

bool TheoryArrays::preNotifyFact(
    TNode atom, bool pol, TNode fact, bool isPrereg, bool isInternal)
{
  if (!isInternal && !isPrereg)
  {
    if (atom.getKind() == kind::EQUAL)
    {
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
  return false;
}

void TheoryArrays::notifyFact(TNode atom, bool pol, TNode fact, bool isInternal)
{
  // if a disequality
  if (atom.getKind() == kind::EQUAL && !pol && !isInternal)
  {
    // Notice that this should be an external assertion, since we do not
    // internally infer disequalities.
    // Apply ArrDiseq Rule if diseq is between arrays
    if (fact[0][0].getType().isArray() && !d_state.isInConflict())
    {
      NodeManager* nm = NodeManager::currentNM();

      TNode k;
      // k is the skolem for this disequality.
      Trace("pf::array") << "Check: kind::NOT: array theory making a skolem"
                          << std::endl;

      // If not in replay mode, generate a fresh skolem variable
      k = getSkolem(fact);

      Node ak = nm->mkNode(kind::SELECT, fact[0][0], k);
      Node bk = nm->mkNode(kind::SELECT, fact[0][1], k);
      Node eq = ak.eqNode(bk);
      Node lemma = fact[0].orNode(eq.notNode());

      if (options().arrays.arraysPropagate > 0 && d_equalityEngine->hasTerm(ak)
          && d_equalityEngine->hasTerm(bk))
      {
        // Propagate witness disequality - might produce a conflict
        Trace("pf::array") << "Asserting to the equality engine:" << std::endl
                           << "\teq = " << eq << std::endl
                           << "\treason = " << fact << std::endl;
        d_im.assertInference(eq, false, InferenceId::ARRAYS_EXT, fact, PfRule::ARRAYS_EXT);
        ++d_numProp;
      }

      // If this is the solution pass, generate the lemma. Otherwise, don't
      // generate it - as this is the lemma that we're reproving...
      Trace("arrays-lem") << "Arrays::addExtLemma " << lemma << "\n";
      d_im.arrayLemma(eq.notNode(), InferenceId::ARRAYS_EXT, fact, PfRule::ARRAYS_EXT);
      ++d_numExt;
    }
    else
    {
      Trace("pf::array") << "Check: kind::NOT: array theory NOT making a skolem"
                         << std::endl;
      d_modelConstraints.push_back(fact);
    }
  }
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

  NodeBuilder conjunction(invert ? kind::OR : kind::AND);
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
  if (options().arrays.arraysWeakEquivalence) return;
  if (d_infoMap.isNonLinear(a)) return;

  Trace("arrays") << spaces(context()->getLevel()) << "Arrays::setNonLinear ("
                  << a << ")\n";
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
      Trace("arrays-lem") << spaces(context()->getLevel())
                          << "Arrays::setNonLinear (" << store << ", " << c
                          << ", " << j << ", " << i << ")\n";
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
  bool optLinear = options().arrays.arraysOptimizeLinear;
  bool weakEquiv = options().arrays.arraysWeakEquivalence;

  Node n;
  while (true) {
    // Normally, a is its own representative, but it's possible for a to have
    // been merged with another array after it got queued up by the equality engine,
    // so we take its representative to be safe.
    a = d_equalityEngine->getRepresentative(a);
    Assert(d_equalityEngine->getRepresentative(b) == a);
    Trace("arrays-merge") << spaces(context()->getLevel()) << "Arrays::merge: ("
                          << a << ", " << b << ")\n";

    if (optLinear && !weakEquiv)
    {
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

    if (weakEquiv)
    {
      d_arrayMerges.push_back(a.eqNode(b));
    }

    // If no more to do, break
    if (d_state.isInConflict() || d_mergeQueue.empty())
    {
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

void TheoryArrays::checkStore(TNode a)
{
  if (options().arrays.arraysWeakEquivalence) return;

  Trace("arrays-cri")<<"Arrays::checkStore "<<a<<"\n";

  if(TraceIsOn("arrays-cri")) {
    d_infoMap.getInfo(a)->print();
  }
  Assert(a.getType().isArray());
  Assert(a.getKind() == kind::STORE);
  TNode b = a[0];
  TNode i = a[1];

  TNode brep = d_equalityEngine->getRepresentative(b);

  if (!options().arrays.arraysOptimizeLinear || d_infoMap.isNonLinear(brep))
  {
    const CTNodeList* js = d_infoMap.getIndices(brep);
    size_t it = 0;
    RowLemmaType lem;
    for(; it < js->size(); ++it) {
      TNode j = (*js)[it];
      if (i == j) continue;
      lem = std::make_tuple(a, b, i, j);
      Trace("arrays-lem") << spaces(context()->getLevel())
                          << "Arrays::checkStore (" << a << ", " << b << ", "
                          << i << ", " << j << ")\n";
      queueRowLemma(lem);
    }
  }
}

void TheoryArrays::checkRowForIndex(TNode i, TNode a)
{
  if (options().arrays.arraysWeakEquivalence) return;

  Trace("arrays-cri")<<"Arrays::checkRowForIndex "<<a<<"\n";
  Trace("arrays-cri")<<"                   index "<<i<<"\n";

  if(TraceIsOn("arrays-cri")) {
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
    // not currently supported in proofs, use THEORY_INFERENCE
    d_im.assertInference(selConst.eqNode(defValue),
                         true,
                         InferenceId::ARRAYS_CONST_ARRAY_DEFAULT,
                         d_true,
                         PfRule::THEORY_INFERENCE);
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
    Trace("arrays-lem") << spaces(context()->getLevel())
                        << "Arrays::checkRowForIndex (" << store << ", "
                        << store[0] << ", " << j << ", " << i << ")\n";
    queueRowLemma(lem);
  }

  if (!options().arrays.arraysOptimizeLinear || d_infoMap.isNonLinear(a))
  {
    it = 0;
    for(; it < instores->size(); ++it) {
      TNode instore = (*instores)[it];
      Assert(instore.getKind() == kind::STORE);
      TNode j = instore[1];
      if (i == j) continue;
      lem = std::make_tuple(instore, instore[0], j, i);
      Trace("arrays-lem") << spaces(context()->getLevel())
                          << "Arrays::checkRowForIndex (" << instore << ", "
                          << instore[0] << ", " << j << ", " << i << ")\n";
      queueRowLemma(lem);
    }
  }
}


// a just became equal to b
// look for new ROW lemmas
void TheoryArrays::checkRowLemmas(TNode a, TNode b)
{
  if (options().arrays.arraysWeakEquivalence) return;

  Trace("arrays-crl")<<"Arrays::checkLemmas begin \n"<<a<<"\n";
  if(TraceIsOn("arrays-crl"))
    d_infoMap.getInfo(a)->print();
  Trace("arrays-crl")<<"  ------------  and "<<b<<"\n";
  if(TraceIsOn("arrays-crl"))
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
      Trace("arrays-lem") << spaces(context()->getLevel())
                          << "Arrays::checkRowLemmas (" << store << ", " << c
                          << ", " << j << ", " << i << ")\n";
      queueRowLemma(lem);
    }
  }

  if (!options().arrays.arraysOptimizeLinear || d_infoMap.isNonLinear(b))
  {
    for(it = 0 ; it < i_a->size(); ++it ) {
      TNode i = (*i_a)[it];
      its = 0;
      for ( ; its < inst_b->size(); ++its) {
        TNode store = (*inst_b)[its];
        Assert(store.getKind() == kind::STORE);
        TNode j = store[1];
        TNode c = store[0];
        lem = std::make_tuple(store, c, j, i);
        Trace("arrays-lem")
            << spaces(context()->getLevel()) << "Arrays::checkRowLemmas ("
            << store << ", " << c << ", " << j << ", " << i << ")\n";
        queueRowLemma(lem);
      }
    }
  }
  Trace("arrays-crl")<<"Arrays::checkLemmas done.\n";
}

void TheoryArrays::propagateRowLemma(RowLemmaType lem)
{
  Trace("pf::array") << "TheoryArrays: RowLemma Propagate called. "
                        "arraysPropagate = "
                     << options().arrays.arraysPropagate << std::endl;

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
  int64_t prop = options().arrays.arraysPropagate;
  if (prop > 0) {
    if (d_equalityEngine->areDisequal(i, j, true) && (bothExist || prop > 1))
    {
      Trace("arrays-lem") << spaces(context()->getLevel())
                          << "Arrays::queueRowLemma: propagating aj = bj ("
                          << aj << ", " << bj << ")\n";
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
      d_im.assertInference(
          aj_eq_bj, true, InferenceId::ARRAYS_READ_OVER_WRITE, reason, PfRule::ARRAYS_READ_OVER_WRITE);
      ++d_numProp;
      return;
    }
    if (bothExist && d_equalityEngine->areDisequal(aj, bj, true))
    {
      Trace("arrays-lem") << spaces(context()->getLevel())
                          << "Arrays::queueRowLemma: propagating i = j (" << i
                          << ", " << j << ")\n";
      Node reason =
          (aj.isConst() && bj.isConst()) ? d_true : aj.eqNode(bj).notNode();
      Node j_eq_i = j.eqNode(i);
      d_im.assertInference(
          j_eq_i, true, InferenceId::ARRAYS_READ_OVER_WRITE_CONTRA, reason, PfRule::ARRAYS_READ_OVER_WRITE_CONTRA);
      ++d_numProp;
      return;
    }
  }
}

void TheoryArrays::queueRowLemma(RowLemmaType lem)
{
  Trace("pf::array") << "Array solver: queue row lemma called" << std::endl;

  if (d_state.isInConflict() || d_RowAlreadyAdded.contains(lem))
  {
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
  int64_t prop = options().arrays.arraysPropagate;

  if (prop > 0) {
    propagateRowLemma(lem);
  }

  // Prefer equality between indexes so as not to introduce new read terms
  if (options().arrays.arraysEagerIndexSplitting && !bothExist
      && !d_equalityEngine->areDisequal(i, j, false))
  {
    Node i_eq_j;
    i_eq_j = d_valuation.ensureLiteral(i.eqNode(j));  // TODO: think about this
#if 0
    i_eq_j = i.eqNode(j);
#endif
    getOutputChannel().requirePhase(i_eq_j, true);
    d_decisionRequests.push(i_eq_j);
  }

  // TODO: maybe add triggers here

  if (options().arrays.arraysEagerLemmas || bothExist)
  {
    // Make sure that any terms introduced by rewriting are appropriately stored in the equality database
    Node aj2 = rewrite(aj);
    if (aj != aj2) {
      if (!ajExists) {
        preRegisterTermInternal(aj);
      }
      if (!d_equalityEngine->hasTerm(aj2))
      {
        preRegisterTermInternal(aj2);
      }
      d_im.assertInference(aj.eqNode(aj2),
                           true,
                           InferenceId::ARRAYS_EQ_TAUTOLOGY,
                           d_true,
                           PfRule::MACRO_SR_PRED_INTRO);
    }
    Node bj2 = rewrite(bj);
    if (bj != bj2) {
      if (!bjExists) {
        preRegisterTermInternal(bj);
      }
      if (!d_equalityEngine->hasTerm(bj2))
      {
        preRegisterTermInternal(bj2);
      }
      d_im.assertInference(bj.eqNode(bj2),
                           true,
                           InferenceId::ARRAYS_EQ_TAUTOLOGY,
                           d_true,
                           PfRule::MACRO_SR_PRED_INTRO);
    }
    if (aj2 == bj2) {
      return;
    }

    // construct lemma
    Node eq1 = aj2.eqNode(bj2);
    Node eq1_r = rewrite(eq1);
    if (eq1_r == d_true) {
      if (!d_equalityEngine->hasTerm(aj2))
      {
        preRegisterTermInternal(aj2);
      }
      if (!d_equalityEngine->hasTerm(bj2))
      {
        preRegisterTermInternal(bj2);
      }
      d_im.assertInference(eq1,
                           true,
                           InferenceId::ARRAYS_EQ_TAUTOLOGY,
                           d_true,
                           PfRule::MACRO_SR_PRED_INTRO);
      return;
    }

    Node eq2 = i.eqNode(j);
    Node eq2_r = rewrite(eq2);
    if (eq2_r == d_true) {
      d_im.assertInference(eq2,
                           true,
                           InferenceId::ARRAYS_EQ_TAUTOLOGY,
                           d_true,
                           PfRule::MACRO_SR_PRED_INTRO);
      return;
    }

    Node lemma = nm->mkNode(kind::OR, eq2_r, eq1_r);

    Trace("arrays-lem") << "Arrays::addRowLemma (1) adding " << lemma << "\n";
    d_RowAlreadyAdded.insert(lem);
    // use non-rewritten nodes
    d_im.arrayLemma(
        aj.eqNode(bj), InferenceId::ARRAYS_READ_OVER_WRITE, eq2.notNode(), PfRule::ARRAYS_READ_OVER_WRITE);
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
  bool reduceSharing = options().arrays.arraysReduceSharing;
  bool lemmasAdded = false;

  for (size_t count = 0, sz = d_RowQueue.size(); count < sz; ++count)
  {
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

    int64_t prop = options().arrays.arraysPropagate;
    if (prop > 0) {
      propagateRowLemma(l);
      if (d_state.isInConflict())
      {
        return true;
      }
    }

    // Make sure that any terms introduced by rewriting are appropriately stored in the equality database
    Node aj2 = rewrite(aj);
    if (aj != aj2) {
      if (!ajExists) {
        preRegisterTermInternal(aj);
      }
      if (!d_equalityEngine->hasTerm(aj2))
      {
        preRegisterTermInternal(aj2);
      }
      d_im.assertInference(aj.eqNode(aj2),
                           true,
                           InferenceId::ARRAYS_EQ_TAUTOLOGY,
                           d_true,
                           PfRule::MACRO_SR_PRED_INTRO);
    }
    Node bj2 = rewrite(bj);
    if (bj != bj2) {
      if (!bjExists) {
        preRegisterTermInternal(bj);
      }
      if (!d_equalityEngine->hasTerm(bj2))
      {
        preRegisterTermInternal(bj2);
      }
      d_im.assertInference(bj.eqNode(bj2),
                           true,
                           InferenceId::ARRAYS_EQ_TAUTOLOGY,
                           d_true,
                           PfRule::MACRO_SR_PRED_INTRO);
    }
    if (aj2 == bj2) {
      continue;
    }

    // construct lemma
    Node eq1 = aj2.eqNode(bj2);
    Node eq1_r = rewrite(eq1);
    if (eq1_r == d_true) {
      if (!d_equalityEngine->hasTerm(aj2))
      {
        preRegisterTermInternal(aj2);
      }
      if (!d_equalityEngine->hasTerm(bj2))
      {
        preRegisterTermInternal(bj2);
      }
      d_im.assertInference(eq1,
                           true,
                           InferenceId::ARRAYS_EQ_TAUTOLOGY,
                           d_true,
                           PfRule::MACRO_SR_PRED_INTRO);
      continue;
    }

    Node eq2 = i.eqNode(j);
    Node eq2_r = rewrite(eq2);
    if (eq2_r == d_true) {
      d_im.assertInference(eq2,
                           true,
                           InferenceId::ARRAYS_EQ_TAUTOLOGY,
                           d_true,
                           PfRule::MACRO_SR_PRED_INTRO);
      continue;
    }

    Node lem = nm->mkNode(kind::OR, eq2_r, eq1_r);

    Trace("arrays-lem") << "Arrays::addRowLemma (2) adding " << lem << "\n";
    d_RowAlreadyAdded.insert(l);
    // use non-rewritten nodes, theory preprocessing will rewrite
    d_im.arrayLemma(
        aj.eqNode(bj), InferenceId::ARRAYS_READ_OVER_WRITE, eq2.notNode(), PfRule::ARRAYS_READ_OVER_WRITE);
    ++d_numRow;
    lemmasAdded = true;
    if (reduceSharing)
    {
      return true;
    }
  }
  return lemmasAdded;
}

void TheoryArrays::conflict(TNode a, TNode b) {
  Trace("pf::array") << "TheoryArrays::Conflict called" << std::endl;
  d_im.conflictEqConstantMerge(a, b);
}

TheoryArrays::TheoryArraysDecisionStrategy::TheoryArraysDecisionStrategy(
    TheoryArrays* ta)
    : DecisionStrategy(ta->d_env), d_ta(ta)
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

void TheoryArrays::computeRelevantTerms(std::set<Node>& termSet)
{
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

}  // namespace arrays
}  // namespace theory
}  // namespace cvc5::internal
