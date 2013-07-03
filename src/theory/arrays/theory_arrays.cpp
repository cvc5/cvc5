/*********************                                                        */
/*! \file theory_arrays.cpp
 ** \verbatim
 ** Original author: Clark Barrett
 ** Major contributors: Morgan Deters
 ** Minor contributors (to current version): Tim King, Andrew Reynolds, Dejan Jovanovic
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2013  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief Implementation of the theory of arrays.
 **
 ** Implementation of the theory of arrays.
 **/


#include "theory/arrays/theory_arrays.h"
#include "theory/valuation.h"
#include "expr/kind.h"
#include <map>
#include "theory/rewriter.h"
#include "expr/command.h"
#include "theory/theory_model.h"
#include "theory/arrays/options.h"
#include "smt/logic_exception.h"


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
const bool d_propagateLemmas = true;
const bool d_preprocess = true;
const bool d_solveWrite = true;
const bool d_solveWrite2 = false;
  // These are now options
  //bool d_useNonLinearOpt = true;
  //bool d_lazyRIntro1 = true;
  //bool d_eagerIndexSplitting = false;

TheoryArrays::TheoryArrays(context::Context* c, context::UserContext* u, OutputChannel& out, Valuation valuation, const LogicInfo& logicInfo, QuantifiersEngine* qe) :
  Theory(THEORY_ARRAY, c, u, out, valuation, logicInfo, qe),
  d_numRow("theory::arrays::number of Row lemmas", 0),
  d_numExt("theory::arrays::number of Ext lemmas", 0),
  d_numProp("theory::arrays::number of propagations", 0),
  d_numExplain("theory::arrays::number of explanations", 0),
  d_numNonLinear("theory::arrays::number of calls to setNonLinear", 0),
  d_numSharedArrayVarSplits("theory::arrays::number of shared array var splits", 0),
  d_numGetModelValSplits("theory::arrays::number of getModelVal splits", 0),
  d_numGetModelValConflicts("theory::arrays::number of getModelVal conflicts", 0),
  d_numSetModelValSplits("theory::arrays::number of setModelVal splits", 0),
  d_numSetModelValConflicts("theory::arrays::number of setModelVal conflicts", 0),
  d_checkTimer("theory::arrays::checkTime"),
  d_ppEqualityEngine(u, "theory::arrays::TheoryArraysPP"),
  d_ppFacts(u),
  //  d_ppCache(u),
  d_literalsToPropagate(c),
  d_literalsToPropagateIndex(c, 0),
  d_isPreRegistered(c),
  d_mayEqualEqualityEngine(c, "theory::arrays::TheoryArraysMayEqual"),
  d_notify(*this),
  d_equalityEngine(d_notify, c, "theory::arrays::TheoryArrays"),
  d_conflict(c, false),
  d_backtracker(c),
  d_infoMap(c, &d_backtracker),
  d_mergeQueue(c),
  d_mergeInProgress(false),
  d_RowQueue(c),
  d_RowAlreadyAdded(u),
  d_sharedArrays(c),
  d_sharedOther(c),
  d_sharedTerms(c, false),
  d_reads(c),
  d_skolemIndex(c, 0),
  d_decisionRequests(c),
  d_permRef(c),
  d_modelConstraints(c),
  d_lemmasSaved(c),
  d_inCheckModel(false)
{
  StatisticsRegistry::registerStat(&d_numRow);
  StatisticsRegistry::registerStat(&d_numExt);
  StatisticsRegistry::registerStat(&d_numProp);
  StatisticsRegistry::registerStat(&d_numExplain);
  StatisticsRegistry::registerStat(&d_numNonLinear);
  StatisticsRegistry::registerStat(&d_numSharedArrayVarSplits);
  StatisticsRegistry::registerStat(&d_numGetModelValSplits);
  StatisticsRegistry::registerStat(&d_numGetModelValConflicts);
  StatisticsRegistry::registerStat(&d_numSetModelValSplits);
  StatisticsRegistry::registerStat(&d_numSetModelValConflicts);
  StatisticsRegistry::registerStat(&d_checkTimer);

  d_true = NodeManager::currentNM()->mkConst<bool>(true);
  d_false = NodeManager::currentNM()->mkConst<bool>(false);

  // The preprocessing congruence kinds
  d_ppEqualityEngine.addFunctionKind(kind::SELECT);
  d_ppEqualityEngine.addFunctionKind(kind::STORE);

  // The mayequal congruence kinds
  d_mayEqualEqualityEngine.addFunctionKind(kind::SELECT);
  d_mayEqualEqualityEngine.addFunctionKind(kind::STORE);

  // The kinds we are treating as function application in congruence
  d_equalityEngine.addFunctionKind(kind::SELECT);
  if (d_ccStore) {
    d_equalityEngine.addFunctionKind(kind::STORE);
  }
  if (d_useArrTable) {
    d_equalityEngine.addFunctionKind(kind::ARR_TABLE_FUN);
  }
}

TheoryArrays::~TheoryArrays() {

  StatisticsRegistry::unregisterStat(&d_numRow);
  StatisticsRegistry::unregisterStat(&d_numExt);
  StatisticsRegistry::unregisterStat(&d_numProp);
  StatisticsRegistry::unregisterStat(&d_numExplain);
  StatisticsRegistry::unregisterStat(&d_numNonLinear);
  StatisticsRegistry::unregisterStat(&d_numSharedArrayVarSplits);
  StatisticsRegistry::unregisterStat(&d_numGetModelValSplits);
  StatisticsRegistry::unregisterStat(&d_numGetModelValConflicts);
  StatisticsRegistry::unregisterStat(&d_numSetModelValSplits);
  StatisticsRegistry::unregisterStat(&d_numSetModelValConflicts);
  StatisticsRegistry::unregisterStat(&d_checkTimer);

}

void TheoryArrays::setMasterEqualityEngine(eq::EqualityEngine* eq) {
  d_equalityEngine.setMasterEqualityEngine(eq);
}


/////////////////////////////////////////////////////////////////////////////
// PREPROCESSING
/////////////////////////////////////////////////////////////////////////////


bool TheoryArrays::ppDisequal(TNode a, TNode b) {
  bool termsExist = d_ppEqualityEngine.hasTerm(a) && d_ppEqualityEngine.hasTerm(b);
  Assert(!termsExist || !a.isConst() || !b.isConst() || a == b || d_ppEqualityEngine.areDisequal(a, b, false));
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
            Node hyp2(index_i.getType() == nm->booleanType()?
                      index_i.iffNode(index_j) : index_i.eqNode(index_j));
            hyp << hyp2.notNode();
          }
          write_j = write_j[0];
        }

        Node r1 = nm->mkNode(kind::SELECT, e1, index_i);
        conc = (r1.getType() == nm->booleanType())?
          r1.iffNode(write_i[2]) : r1.eqNode(write_i[2]);
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


Node TheoryArrays::ppRewrite(TNode term) {
  if (!d_preprocess) return term;
  d_ppEqualityEngine.addTerm(term);
  switch (term.getKind()) {
    case kind::SELECT: {
      // select(store(a,i,v),j) = select(a,j)
      //    IF i != j
      if (term[0].getKind() == kind::STORE && ppDisequal(term[0][1], term[1])) {
        return NodeBuilder<2>(kind::SELECT) << term[0][0] << term[1];
      }
      break;
    }
    case kind::STORE: {
      // store(store(a,i,v),j,w) = store(store(a,j,w),i,v)
      //    IF i != j and j comes before i in the ordering
      if (term[0].getKind() == kind::STORE && (term[1] < term[0][1]) && ppDisequal(term[1],term[0][1])) {
        Node inner = NodeBuilder<3>(kind::STORE) << term[0][0] << term[1] << term[2];
        Node outer = NodeBuilder<3>(kind::STORE) << inner << term[0][1] << term[0][2];
        return outer;
      }
      break;
    }
    case kind::EQUAL: {
      return solveWrite(term, d_solveWrite, d_solveWrite2, true);
      break;
    }
    default:
      break;
  }
  return term;
}


Theory::PPAssertStatus TheoryArrays::ppAssert(TNode in, SubstitutionMap& outSubstitutions) {
  switch(in.getKind()) {
    case kind::EQUAL:
    {
      d_ppFacts.push_back(in);
      d_ppEqualityEngine.assertEquality(in, true, in);
      if (in[0].isVar() && !in[1].hasSubterm(in[0])) {
        outSubstitutions.addSubstitution(in[0], in[1]);
        return PP_ASSERT_STATUS_SOLVED;
      }
      if (in[1].isVar() && !in[0].hasSubterm(in[1])) {
        outSubstitutions.addSubstitution(in[1], in[0]);
        return PP_ASSERT_STATUS_SOLVED;
      }
      break;
    }
    case kind::NOT:
    {
      d_ppFacts.push_back(in);
      Assert(in[0].getKind() == kind::EQUAL ||
             in[0].getKind() == kind::IFF );
      Node a = in[0][0];
      Node b = in[0][1];
      d_ppEqualityEngine.assertEquality(in[0], false, in);
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


void TheoryArrays::explain(TNode literal, std::vector<TNode>& assumptions) {
  // Do the work
  bool polarity = literal.getKind() != kind::NOT;
  TNode atom = polarity ? literal : literal[0];
  if (atom.getKind() == kind::EQUAL || atom.getKind() == kind::IFF) {
    d_equalityEngine.explainEquality(atom[0], atom[1], polarity, assumptions);
  } else {
    d_equalityEngine.explainPredicate(atom, polarity, assumptions);
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
    d_equalityEngine.addTriggerEquality(node);
    break;
  case kind::SELECT: {
    // Invariant: array terms should be preregistered before being added to the equality engine
    if (d_equalityEngine.hasTerm(node)) {
      Assert(d_isPreRegistered.find(node) != d_isPreRegistered.end());
      return;
    }
    // Reads
    TNode store = d_equalityEngine.getRepresentative(node[0]);

    // The may equal needs the store
    d_mayEqualEqualityEngine.addTerm(store);

    if (options::arraysLazyRIntro1()) {
      // Apply RIntro1 rule to any stores equal to store if not done already
      const CTNodeList* stores = d_infoMap.getStores(store);
      CTNodeList::const_iterator it = stores->begin();
      if (it != stores->end()) {
        NodeManager* nm = NodeManager::currentNM();
        TNode s = *it;
        if (!d_infoMap.rIntro1Applied(s)) {
          d_infoMap.setRIntro1Applied(s);
          Assert(s.getKind()==kind::STORE);
          Node ni = nm->mkNode(kind::SELECT, s, s[1]);
          if (ni != node) {
            preRegisterTermInternal(ni);
          }
          d_equalityEngine.assertEquality(ni.eqNode(s[2]), true, d_true);
          Assert(++it == stores->end());
        }
      }
    }

    if (node.getType().isArray()) {
      d_equalityEngine.addTriggerTerm(node, THEORY_ARRAY);
    }
    else {
      d_equalityEngine.addTerm(node);
    }
    // Maybe it's a predicate
    // TODO: remove this or keep it if we allow Boolean elements in arrays.
    if (node.getType().isBoolean()) {
      // Get triggered for both equal and dis-equal
      d_equalityEngine.addTriggerPredicate(node);
    }

    Assert(d_equalityEngine.getRepresentative(store) == store);
    d_infoMap.addIndex(store, node[1]);
    d_reads.push_back(node);
    Assert((d_isPreRegistered.insert(node), true));
    checkRowForIndex(node[1], store);
    break;
  }
  case kind::STORE: {
    // Invariant: array terms should be preregistered before being added to the equality engine
    if (d_equalityEngine.hasTerm(node)) {
      break;
    }
    d_equalityEngine.addTriggerTerm(node, THEORY_ARRAY);

    TNode a = d_equalityEngine.getRepresentative(node[0]);

    d_mayEqualEqualityEngine.assertEquality(node.eqNode(a), true, d_true);

    if (!options::arraysLazyRIntro1()) {
      TNode i = node[1];
      TNode v = node[2];
      NodeManager* nm = NodeManager::currentNM();
      Node ni = nm->mkNode(kind::SELECT, node, i);
      if (!d_equalityEngine.hasTerm(ni)) {
        preRegisterTermInternal(ni);
      }

      // Apply RIntro1 Rule
      d_equalityEngine.assertEquality(ni.eqNode(v), true, d_true);
    }

    d_infoMap.addStore(node, node);
    d_infoMap.addInStore(a, node);
    d_infoMap.setModelRep(node, node);

    checkStore(node);
    break;
  }
  case kind::STORE_ALL: {
    throw LogicException("Array theory solver does not yet support assertions using constant array value");
  }
  default:
    // Variables etc
    if (node.getType().isArray()) {
      d_equalityEngine.addTriggerTerm(node, THEORY_ARRAY);
      Assert(d_equalityEngine.getSize(node) == 1);
    }
    else {
      d_equalityEngine.addTerm(node);
    }
    break;
  }
  // Invariant: preregistered terms are exactly the terms in the equality engine
  // Disabled, see comment above for kind::EQUAL
  // Assert(d_equalityEngine.hasTerm(node) || !d_equalityEngine.consistent());
}


void TheoryArrays::preRegisterTerm(TNode node)
{
  preRegisterTermInternal(node);
}


void TheoryArrays::propagate(Effort e)
{
  // direct propagation now
}


Node TheoryArrays::explain(TNode literal)
{
  ++d_numExplain;
  Debug("arrays") << spaces(getSatContext()->getLevel()) << "TheoryArrays::explain(" << literal << ")" << std::endl;
  std::vector<TNode> assumptions;
  explain(literal, assumptions);
  return mkAnd(assumptions);
}


/////////////////////////////////////////////////////////////////////////////
// SHARING
/////////////////////////////////////////////////////////////////////////////


void TheoryArrays::addSharedTerm(TNode t) {
  Debug("arrays::sharing") << spaces(getSatContext()->getLevel()) << "TheoryArrays::addSharedTerm(" << t << ")" << std::endl;
  d_equalityEngine.addTriggerTerm(t, THEORY_ARRAY);
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
  Assert(d_equalityEngine.hasTerm(a) && d_equalityEngine.hasTerm(b));
  if (d_equalityEngine.areEqual(a, b)) {
    // The terms are implied to be equal
    return EQUALITY_TRUE;
  }
  if (d_equalityEngine.areDisequal(a, b, false)) {
    // The terms are implied to be dis-equal
    return EQUALITY_FALSE;
  }
  //TODO: can we be more precise sometimes?
  return EQUALITY_UNKNOWN;
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
        Assert(d_valuation.getEqualityStatus((*it1), (*it2)) == EQUALITY_UNKNOWN);
        addCarePair((*it1), (*it2));
        ++d_numSharedArrayVarSplits;
        return;
      }
    }
  }
  if (options::arraysModelBased()) {
    checkModel(EFFORT_COMBINATION);
    return;
  }
  if (d_sharedTerms) {

    vector< pair<TNode, TNode> > currentPairs;

    // Go through the read terms and see if there are any to split on
    unsigned size = d_reads.size();
    for (unsigned i = 0; i < size; ++ i) {
      TNode r1 = d_reads[i];

      // Make sure shared terms were identified correctly
      // Assert(theoryOf(r1[0]) == THEORY_ARRAY || isShared(r1[0]));
      // Assert(theoryOf(r1[1]) == THEORY_ARRAY ||
      //        d_sharedOther.find(r1[1]) != d_sharedOther.end());

      for (unsigned j = i + 1; j < size; ++ j) {
        TNode r2 = d_reads[j];

        Debug("arrays::sharing") << "TheoryArrays::computeCareGraph(): checking reads " << r1 << " and " << r2 << std::endl;

        // If the terms are already known to be equal, we are also in good shape
        if (d_equalityEngine.hasTerm(r1) && d_equalityEngine.hasTerm(r2) && d_equalityEngine.areEqual(r1, r2)) {
          Debug("arrays::sharing") << "TheoryArrays::computeCareGraph(): equal, skipping" << std::endl;
          continue;
        }

        if (r1[0] != r2[0]) {
          // If arrays are known to be disequal, or cannot become equal, we can continue
          Assert(d_mayEqualEqualityEngine.hasTerm(r1[0]) && d_mayEqualEqualityEngine.hasTerm(r2[0]));
          if (r1[0].getType() != r2[0].getType() ||
              d_equalityEngine.areDisequal(r1[0], r2[0], false)) {
            Debug("arrays::sharing") << "TheoryArrays::computeCareGraph(): arrays can't be equal, skipping" << std::endl;
            continue;
          }
          else if (!d_mayEqualEqualityEngine.areEqual(r1[0], r2[0])) {
            if (r2.getType().getCardinality().isInfinite()) {
              continue;
            }
            // TODO: add a disequality split for these two arrays
            continue;
          }
        }

        TNode x = r1[1];
        TNode y = r2[1];

        if (!d_equalityEngine.isTriggerTerm(x, THEORY_ARRAY) || !d_equalityEngine.isTriggerTerm(y, THEORY_ARRAY)) {
          Debug("arrays::sharing") << "TheoryArrays::computeCareGraph(): not connected to shared terms, skipping" << std::endl;
          continue;
        }

        EqualityStatus eqStatus = getEqualityStatus(x, y);

        if (eqStatus != EQUALITY_UNKNOWN) {
          Debug("arrays::sharing") << "TheoryArrays::computeCareGraph(): equality status known, skipping" << std::endl;
          continue;
        }

        // Get representative trigger terms
        TNode x_shared = d_equalityEngine.getTriggerTermRepresentative(x, THEORY_ARRAY);
        TNode y_shared = d_equalityEngine.getTriggerTermRepresentative(y, THEORY_ARRAY);
        EqualityStatus eqStatusDomain = d_valuation.getEqualityStatus(x_shared, y_shared);
        switch (eqStatusDomain) {
          case EQUALITY_TRUE_AND_PROPAGATED:
            // Should have been propagated to us
            Assert(false);
            break;
          case EQUALITY_FALSE_AND_PROPAGATED:
            // Should have been propagated to us
            Assert(false);
            break;
          case EQUALITY_FALSE:
          case EQUALITY_TRUE:
            // Missed propagation - need to add the pair so that theory engine can force propagation
            Debug("arrays::sharing") << "TheoryArrays::computeCareGraph(): missed propagation" << std::endl;
            break;
          case EQUALITY_FALSE_IN_MODEL:
            Debug("arrays::sharing") << "TheoryArrays::computeCareGraph(): false in model" << std::endl;
            break;
          default:
            break;
        }


        // Otherwise, add this pair
        Debug("arrays::sharing") << "TheoryArrays::computeCareGraph(): adding to care-graph" << std::endl;
        addCarePair(x_shared, y_shared);
      }
    }
  }
}


/////////////////////////////////////////////////////////////////////////////
// MODEL GENERATION
/////////////////////////////////////////////////////////////////////////////


void TheoryArrays::collectModelInfo( TheoryModel* m, bool fullModel )
{
  set<Node> termSet;

  // Compute terms appearing in assertions and shared terms
  computeRelevantTerms(termSet);

  // Compute arrays that we need to produce representatives for and also make sure RIntro1 reads are included in the relevant set of reads
  NodeManager* nm = NodeManager::currentNM();
  std::vector<Node> arrays;
  bool computeRep, isArray;
  eq::EqClassesIterator eqcs_i = eq::EqClassesIterator(&d_equalityEngine);
  for (; !eqcs_i.isFinished(); ++eqcs_i) {
    Node eqc = (*eqcs_i);
    isArray = eqc.getType().isArray();
    if (!isArray) {
      continue;
    }
    computeRep = false;
    eq::EqClassIterator eqc_i = eq::EqClassIterator(eqc, &d_equalityEngine);
    for (; !eqc_i.isFinished(); ++eqc_i) {
      Node n = *eqc_i;
      // If this EC is an array type and it contains something other than STORE nodes, we have to compute a representative explicitly
      if (isArray && termSet.find(n) != termSet.end()) {
        if (n.getKind() == kind::STORE) {
          // Make sure RIntro1 reads are included
          Node r = nm->mkNode(kind::SELECT, n, n[1]);
          Trace("arrays::collectModelInfo") << "TheoryArrays::collectModelInfo, adding RIntro1 read: " << r << endl;
          termSet.insert(r);
        }
        else if (!computeRep) {
          arrays.push_back(eqc);
          computeRep = true;
        }
      }
    }
  }

  // Now do a fixed-point iteration to get all reads that need to be included because of RIntro2 rule
  bool changed;
  do {
    changed = false;
    eqcs_i = eq::EqClassesIterator(&d_equalityEngine);
    for (; !eqcs_i.isFinished(); ++eqcs_i) {
      Node eqc = (*eqcs_i);
      eq::EqClassIterator eqc_i = eq::EqClassIterator(eqc, &d_equalityEngine);
      for (; !eqc_i.isFinished(); ++eqc_i) {
        Node n = *eqc_i;
        if (n.getKind() == kind::SELECT && termSet.find(n) != termSet.end()) {

          // Find all terms equivalent to n[0] and get corresponding read terms
          Node array_eqc = d_equalityEngine.getRepresentative(n[0]);
          eq::EqClassIterator array_eqc_i = eq::EqClassIterator(array_eqc, &d_equalityEngine);
          for (; !array_eqc_i.isFinished(); ++array_eqc_i) {
            Node arr = *array_eqc_i;
            if (arr.getKind() == kind::STORE &&
                termSet.find(arr) != termSet.end() &&
                !d_equalityEngine.areEqual(arr[1],n[1])) {
              Node r = nm->mkNode(kind::SELECT, arr, n[1]);
              if (termSet.find(r) == termSet.end() && d_equalityEngine.hasTerm(r)) {
                Trace("arrays::collectModelInfo") << "TheoryArrays::collectModelInfo, adding RIntro2(a) read: " << r << endl;
                termSet.insert(r);
                changed = true;
              }
              r = nm->mkNode(kind::SELECT, arr[0], n[1]);
              if (termSet.find(r) == termSet.end() && d_equalityEngine.hasTerm(r)) {
                Trace("arrays::collectModelInfo") << "TheoryArrays::collectModelInfo, adding RIntro2(b) read: " << r << endl;
                termSet.insert(r);
                changed = true;
              }
            }
          }

          // Find all stores in which n[0] appears and get corresponding read terms
          const CTNodeList* instores = d_infoMap.getInStores(array_eqc);
          size_t it = 0;
          for(; it < instores->size(); ++it) {
            TNode instore = (*instores)[it];
            Assert(instore.getKind()==kind::STORE);
            if (termSet.find(instore) != termSet.end() &&
                !d_equalityEngine.areEqual(instore[1],n[1])) {
              Node r = nm->mkNode(kind::SELECT, instore, n[1]);
              if (termSet.find(r) == termSet.end() && d_equalityEngine.hasTerm(r)) {
                Trace("arrays::collectModelInfo") << "TheoryArrays::collectModelInfo, adding RIntro2(c) read: " << r << endl;
                termSet.insert(r);
                changed = true;
              }
              r = nm->mkNode(kind::SELECT, instore[0], n[1]);
              if (termSet.find(r) == termSet.end() && d_equalityEngine.hasTerm(r)) {
                Trace("arrays::collectModelInfo") << "TheoryArrays::collectModelInfo, adding RIntro2(d) read: " << r << endl;
                termSet.insert(r);
                changed = true;
              }
            }
          }
        }
      }
    }
  } while (changed);

  // Send the equality engine information to the model
  m->assertEqualityEngine(&d_equalityEngine, &termSet);

  // Build a list of all the relevant reads, indexed by the store representative
  std::map<Node, std::vector<Node> > selects;
  set<Node>::iterator set_it = termSet.begin(), set_it_end = termSet.end();
  for (; set_it != set_it_end; ++set_it) {
    Node n = *set_it;
    // If this term is a select, record that the EC rep of its store parameter is being read from using this term
    if (n.getKind() == kind::SELECT) {
      selects[d_equalityEngine.getRepresentative(n[0])].push_back(n);
    }
  }

  Node rep;
  map<Node, Node> defValues;
  map<Node, Node>::iterator it;
  TypeSet defaultValuesSet;

  // Loop through all array equivalence classes that need a representative computed
  for (size_t i=0; i<arrays.size(); ++i) {
    TNode n = arrays[i];

    if (fullModel) {
      // Compute default value for this array - there is one default value for every mayEqual equivalence class
      d_mayEqualEqualityEngine.addTerm(n); // add the term in case it isn't there already
      TNode mayRep = d_mayEqualEqualityEngine.getRepresentative(n);
      it = defValues.find(mayRep);
      // If this mayEqual EC doesn't have a default value associated, get the next available default value for the associated array element type
      if (it == defValues.end()) {
        TypeNode valueType = n.getType().getArrayConstituentType();
        rep = defaultValuesSet.nextTypeEnum(valueType);
        if (rep.isNull()) {
          Assert(defaultValuesSet.getSet(valueType)->begin() != defaultValuesSet.getSet(valueType)->end());
          rep = *(defaultValuesSet.getSet(valueType)->begin());
        }
        Trace("arrays-models") << "New default value = " << rep << endl;
        defValues[mayRep] = rep;
      }
      else {
        rep = (*it).second;
      }

      // Build the STORE_ALL term with the default value
      rep = nm->mkConst(ArrayStoreAll(n.getType().toType(), rep.toExpr()));
    }
    else {
      std::hash_map<Node, Node, NodeHashFunction>::iterator it = d_skolemCache.find(n);
      if (it == d_skolemCache.end()) {
        rep = nm->mkSkolem("array_collect_model_var_$$", n.getType(), "base model variable for array collectModelInfo");
        d_skolemCache[n] = rep;
      }
      else {
        rep = (*it).second;
      }
    }

    // For each read, require that the rep stores the right value
    vector<Node>& reads = selects[n];
    for (unsigned j = 0; j < reads.size(); ++j) {
      rep = nm->mkNode(kind::STORE, rep, reads[j][1], reads[j]);
    }
    m->assertEquality(n, rep, true);
    m->assertRepresentative(rep);
  }
}

/////////////////////////////////////////////////////////////////////////////
// NOTIFICATIONS
/////////////////////////////////////////////////////////////////////////////


void TheoryArrays::presolve()
{
  Trace("arrays")<<"Presolving \n";
}


/////////////////////////////////////////////////////////////////////////////
// MAIN SOLVER
/////////////////////////////////////////////////////////////////////////////


Node TheoryArrays::getSkolem(TNode ref, const string& name, const TypeNode& type, const string& comment, bool makeEqual)
{
  Node skolem;
  std::hash_map<Node, Node, NodeHashFunction>::iterator it = d_skolemCache.find(ref);
  if (it == d_skolemCache.end()) {
    NodeManager* nm = NodeManager::currentNM();
    skolem = nm->mkSkolem(name, type, comment);
    d_skolemCache[ref] = skolem;
  }
  else {
    skolem = (*it).second;
    if (d_equalityEngine.hasTerm(ref) &&
        d_equalityEngine.hasTerm(skolem) &&
        d_equalityEngine.areEqual(ref, skolem)) {
      makeEqual = false;
    }
  }
  preRegisterTermInternal(skolem);
  if (makeEqual) {
    Node d = skolem.eqNode(ref);
    Debug("arrays-model-based") << "Asserting skolem equality " << d << endl;
    d_equalityEngine.assertEquality(d, true, d_true);
    Assert(!d_conflict);
    d_skolemAssertions.push_back(d);
    d_skolemIndex = d_skolemIndex + 1;
  }
  return skolem;
}


void TheoryArrays::check(Effort e) {
  if (done() && !fullEffort(e)) {
    return;
  }
  TimerStat::CodeTimer codeTimer(d_checkTimer);

  while (!done() && !d_conflict)
  {
    // Get all the assertions
    Assertion assertion = get();
    TNode fact = assertion.assertion;

    Debug("arrays") << spaces(getSatContext()->getLevel()) << "TheoryArrays::check(): processing " << fact << std::endl;

    bool polarity = fact.getKind() != kind::NOT;
    TNode atom = polarity ? fact : fact[0];

    if (!assertion.isPreregistered) {
      if (atom.getKind() == kind::EQUAL) {
        if (!d_equalityEngine.hasTerm(atom[0])) {
          Assert(atom[0].isConst());
          d_equalityEngine.addTerm(atom[0]);
        }
        if (!d_equalityEngine.hasTerm(atom[1])) {
          Assert(atom[1].isConst());
          d_equalityEngine.addTerm(atom[1]);
        }
      }
    }

    // Do the work
    switch (fact.getKind()) {
      case kind::EQUAL:
        d_equalityEngine.assertEquality(fact, true, fact);
        if (!fact[0].getType().isArray()) {
          d_modelConstraints.push_back(fact);
        }
        break;
      case kind::SELECT:
        d_equalityEngine.assertPredicate(fact, true, fact);
        d_modelConstraints.push_back(fact);
        break;
      case kind::NOT:
        if (fact[0].getKind() == kind::SELECT) {
          d_equalityEngine.assertPredicate(fact[0], false, fact);
          d_modelConstraints.push_back(fact);
        } else if (!d_equalityEngine.areDisequal(fact[0][0], fact[0][1], false)) {
          // Assert the dis-equality
          d_equalityEngine.assertEquality(fact[0], false, fact);

          // Apply ArrDiseq Rule if diseq is between arrays
          if(fact[0][0].getType().isArray() && !d_conflict) {
            NodeManager* nm = NodeManager::currentNM();
            TypeNode indexType = fact[0][0].getType()[0];
            TNode k = getSkolem(fact,"array_ext_index_$$", indexType, "an extensional lemma index variable from the theory of arrays", false);

            Node ak = nm->mkNode(kind::SELECT, fact[0][0], k);
            Node bk = nm->mkNode(kind::SELECT, fact[0][1], k);
            Node eq = d_valuation.ensureLiteral(ak.eqNode(bk));
            Assert(eq.getKind() == kind::EQUAL);
            Node lemma = fact[0].orNode(eq.notNode());
            Trace("arrays-lem")<<"Arrays::addExtLemma " << lemma <<"\n";
            d_out->lemma(lemma);
            ++d_numExt;
          }
          else {
            d_modelConstraints.push_back(fact);
          }
        }
        break;
      default:
        Unreachable();
    }
  }

  if (options::arraysModelBased() && !d_conflict && (options::arraysEagerIndexSplitting() || fullEffort(e))) {
    checkModel(e);
  }

  if(!options::arraysEagerLemmas() && fullEffort(e) && !d_conflict && !options::arraysModelBased()) {
    // generate the lemmas on the worklist
    Trace("arrays-lem")<<"Arrays::discharging lemmas: "<<d_RowQueue.size()<<"\n";
    dischargeLemmas();
  }

  Trace("arrays") << spaces(getSatContext()->getLevel()) << "Arrays::check(): done" << endl;
}


void TheoryArrays::convertNodeToAssumptions(TNode node, vector<TNode>& assumptions, TNode nodeSkip)
{
  Assert(node.getKind() == kind::AND);
  for(TNode::iterator child_it = node.begin(); child_it != node.end(); ++child_it) {
    if ((*child_it).getKind() == kind::AND) {
      convertNodeToAssumptions(*child_it, assumptions, nodeSkip);
    }
    else if (*child_it != nodeSkip) {
      assumptions.push_back(*child_it);
    }
  }
}


void TheoryArrays::preRegisterStores(TNode s)
{
  if (d_equalityEngine.hasTerm(s)) {
    return;
  }
  if (s.getKind() == kind::STORE) {
    preRegisterStores(s[0]);
    preRegisterTermInternal(s);
  }
}


void TheoryArrays::checkModel(Effort e)
{
  d_inCheckModel = true;
  d_topLevel = getSatContext()->getLevel();
  Assert(d_skolemIndex == 0);
  Assert(d_skolemAssertions.empty());
  Assert(d_lemmas.empty());

  if (combination(e)) {
    // Add constraints for shared terms
    context::CDList<TNode>::const_iterator shared_it = shared_terms_begin(), shared_it_end = shared_terms_end(), shared_it2;
    Node modelVal, modelVal2, d;
    vector<TNode> assumptions;
    for (; shared_it != shared_it_end; ++shared_it) {
      if ((*shared_it).getType().isArray()) {
        continue;
      }
      if ((*shared_it).isConst()) {
        modelVal = (*shared_it);
      }
      else {
        modelVal = d_valuation.getModelValue(*shared_it);
        if (modelVal.isNull()) {
          continue;
        }
      }
      Assert(modelVal.isConst());
      for (shared_it2 = shared_it, ++shared_it2; shared_it2 != shared_it_end; ++shared_it2) {
        if ((*shared_it2).getType() != (*shared_it).getType()) {
          continue;
        }
        if ((*shared_it2).isConst()) {
          modelVal2 = (*shared_it2);
        }
        else {
          modelVal2 = d_valuation.getModelValue(*shared_it2);
          if (modelVal2.isNull()) {
            continue;
          }
        }
        Assert(modelVal2.isConst());
        d = (*shared_it).eqNode(*shared_it2);
        if (modelVal != modelVal2) {
          d = d.notNode();
        }
        if (!setModelVal(d, d_true, false, true, assumptions)) {
          assumptions.push_back(d);
          d_lemmas.push_back(mkAnd(assumptions, true));
          goto finish;
        }
        assumptions.clear();
      }
    }
  }
  {
  // TODO: record and replay decisions
  int baseLevel = getSatContext()->getLevel();
  unsigned constraintIdx;
  Node assertion, assertionToCheck;
  vector<TNode> assumptions;
  int numrestarts = 0;
  while (true || numrestarts < 1 || fullEffort(e) || combination(e)) {
    ++numrestarts;
    d_out->safePoint();
    int level = getSatContext()->getLevel();
    d_getModelValCache.clear();
    for (constraintIdx = 0; constraintIdx < d_modelConstraints.size(); ++constraintIdx) {
      assertion = d_modelConstraints[constraintIdx];
      if (getModelValRec(assertion) != d_true) {
        break;
      }
    }
    getSatContext()->popto(level);
    if (constraintIdx == d_modelConstraints.size()) {
      break;
    }

    if (assertion.getKind() == kind::EQUAL && assertion[0].getType().isArray()) {
      assertionToCheck = solveWrite(expandStores(assertion[0], assumptions).eqNode(expandStores(assertion[1], assumptions)), true, true, false);
      if (assertionToCheck.getKind() == kind::AND &&
          assertionToCheck[assertionToCheck.getNumChildren()-1].getKind() == kind::EQUAL) {
        TNode s = assertionToCheck[assertionToCheck.getNumChildren()-1][0];
        preRegisterStores(s);
      }
    }
    else {
      assertionToCheck = assertion;
    }
    // TODO: try not collecting assumptions the first time
    while (!setModelVal(assertionToCheck, d_true, false, true, assumptions)) {
    restart:
      if (assertion.getKind() == kind::EQUAL) {
        d_equalityEngine.explainEquality(assertion[0], assertion[1], true, assumptions);
      }
      else {
        assumptions.push_back(assertion);
      }
#ifdef CVC4_ASSERTIONS
      std::set<TNode> validAssumptions;
      context::CDList<Assertion>::const_iterator assert_it2 = facts_begin();
      for (; assert_it2 != facts_end(); ++assert_it2) {
        validAssumptions.insert(*assert_it2);
      }
      for (unsigned i = 0; i < d_decisions.size(); ++i) {
        validAssumptions.insert(d_decisions[i]);
      }
#endif
      std::set<TNode> all;
      std::set<TNode> explained;
      unsigned i = 0;
      TNode t;
      for (; i < assumptions.size(); ++i) {
        t = assumptions[i];
        if (t == d_true) {
          continue;
        }
        if (t.getKind() == kind::AND) {
          for(TNode::iterator child_it = t.begin(); child_it != t.end(); ++child_it) {
            Assert(validAssumptions.find(*child_it) != validAssumptions.end());
            all.insert(*child_it);
          }
        }
        // Expand explanation resulting from propagating a ROW lemma
        else if (t.getKind() == kind::OR) {
          if ((explained.find(t) == explained.end())) {
            Assert(t[1].getKind() == kind::EQUAL);
            d_equalityEngine.explainEquality(t[1][0], t[1][1], false, assumptions);
            explained.insert(t);
          }
          continue;
        }
        else {
          Assert(validAssumptions.find(t) != validAssumptions.end());
          all.insert(t);
        }
      }

      bool eq = false;
      Node decision, explanation;
      while (!d_decisions.empty()) {
        getSatContext()->pop();
        decision = d_decisions.back();
        d_decisions.pop_back();
        if (all.find(decision) != all.end()) {
          if (getSatContext()->getLevel() < baseLevel) {
            if (all.size() == 1) {
              d_lemmas.push_back(decision.negate());
            }
            else {
              NodeBuilder<> disjunction(kind::OR);
              std::set<TNode>::const_iterator it = all.begin();
              std::set<TNode>::const_iterator it_end = all.end();
              while (it != it_end) {
                disjunction << (*it).negate();
                ++it;
              }
              d_lemmas.push_back(disjunction);
            }
            goto finish;
          }
          all.erase(decision);
          eq = false;
          if (decision.getKind() == kind::NOT) {
            decision = decision[0];
            eq = true;
          }
          while (getSatContext()->getLevel() != baseLevel && all.find(d_decisions.back()) == all.end()) {
            getSatContext()->pop();
            d_decisions.pop_back();
          }
          break;
        }
        else {
          decision = Node();
        }
      }
      if (all.size() == 0) {
        explanation = d_true;
      }
      if (all.size() == 1) {
        // All the same, or just one
        explanation = *(all.begin());
      }
      else {
        NodeBuilder<> conjunction(kind::AND);
        std::set<TNode>::const_iterator it = all.begin();
        std::set<TNode>::const_iterator it_end = all.end();
        while (it != it_end) {
          conjunction << *it;
          ++it;
        }
        explanation = conjunction;
        d_permRef.push_back(explanation);
      }
      if (decision.isNull()) {
        //        d_lemmas.pop_back();
        d_conflictNode = explanation;
        d_conflict = true;
        break;
      }
      {
        // generate lemma
        if (all.size() == 0) {
          d_lemmas.push_back(decision.negate());
        }
        else {
          NodeBuilder<> disjunction(kind::OR);
          std::set<TNode>::const_iterator it = all.begin();
          std::set<TNode>::const_iterator it_end = all.end();
          while (it != it_end) {
            disjunction << (*it).negate();
            ++it;
          }
          disjunction << decision.negate();
          d_lemmas.push_back(disjunction);
        }
      }
      d_equalityEngine.assertEquality(decision, eq, explanation);
      if (!eq) decision = decision.notNode();
      Debug("arrays-model-based") << "Asserting learned literal " << decision << " with explanation " << explanation << endl;
      if (d_conflict) {
        assumptions.clear();
        convertNodeToAssumptions(d_conflictNode, assumptions, TNode());
        assertion = d_true;
        goto restart;
      }
      assumptions.clear();

      // Reassert skolems if necessary
      Node d;
      while (d_skolemIndex < d_skolemAssertions.size()) {
        d = d_skolemAssertions[d_skolemIndex];
        Assert(isLeaf(d[0]));
        if (!d_equalityEngine.hasTerm(d[0])) {
          preRegisterTermInternal(d[0]);
        }
        if (d[0].getType().isArray()) {
          Assert(d[1].getKind() == kind::STORE);
          if (d[1][0].getKind() == kind::STORE) {
            if (!d_equalityEngine.hasTerm(d[1][0][0])) {
              preRegisterTermInternal(d[1][0][0]);
            }
            if (!d_equalityEngine.hasTerm(d[1][0][2])) {
              preRegisterTermInternal(d[1][0][2]);
            }
          }
          if (!d_equalityEngine.hasTerm(d[1][0])) {
            preRegisterTermInternal(d[1][0]);
          }
          if (!d_equalityEngine.hasTerm(d[1][2])) {
            preRegisterTermInternal(d[1][2]);
          }
          if (!d_equalityEngine.hasTerm(d[1])) {
            preRegisterTermInternal(d[1]);
          }
        }
        Debug("arrays-model-based") << "Re-asserting skolem equality " << d << endl;
        d_equalityEngine.assertEquality(d, true, d_true);
        Assert(!d_conflict);
        if (!d[0].getType().isArray()) {
          if (!setModelVal(d[1], d[0], false, true, assumptions)) {
            assertion = d_true;
            goto restart;
          }
          assumptions.clear();
        }
        d_skolemIndex = d_skolemIndex + 1;
      }
      // Reregister stores
      if (assertionToCheck != assertion &&
          assertionToCheck.getKind() == kind::AND &&
          assertionToCheck[assertionToCheck.getNumChildren()-1].getKind() == kind::EQUAL) {
        TNode s = assertionToCheck[assertionToCheck.getNumChildren()-1][0];
        preRegisterStores(s);
      }
    }
    if (d_conflict) {
      break;
    }
    //    Assert(getModelVal(assertion) == d_true);
    assumptions.clear();
  }
#ifdef CVC4_ASSERTIONS
  if (!d_conflict && fullEffort(e)) {
    context::CDList<Assertion>::const_iterator assert_it = facts_begin(), assert_it_end = facts_end();
    for (; assert_it != assert_it_end; ++assert_it) {
      Assert(getModelVal(*assert_it) == d_true);
    }
  }
#endif
  }
  finish:
  while (!d_decisions.empty()) {
    Assert(!d_conflict);
    getSatContext()->pop();
    d_decisions.pop_back();
  }
  d_skolemAssertions.clear();
  d_skolemIndex = 0;
  while (!d_lemmas.empty()) {
    Debug("arrays-model-based") << "Sending lemma: " << d_lemmas.back() << endl;
    d_out->splitLemma(d_lemmas.back());
#ifdef CVC4_ASSERTIONS
    //    Assert(d_lemmasSaved.find(d_lemmas.back()) == d_lemmasSaved.end());
    //    d_lemmasSaved.insert(d_lemmas.back());
#endif
    d_lemmas.pop_back();
  }
  Assert(getSatContext()->getLevel() == d_topLevel);
  if (d_conflict) {
    Node tmp = d_conflictNode;
    d_out->conflict(tmp);
  }
  d_inCheckModel = false;
}


Node TheoryArrays::getModelVal(TNode node)
{
  int level = getSatContext()->getLevel();
  d_getModelValCache.clear();
  Node ret = getModelValRec(node);
  getSatContext()->popto(level);
  return ret;
}


Node TheoryArrays::getModelValRec(TNode node)
{
  if (node.isConst()) {
    return node;
  }
  NodeMap::iterator it = d_getModelValCache.find(node);
  if (it != d_getModelValCache.end()) {
    return (*it).second;
  }
  Node val;
  switch (node.getKind()) {
    case kind::NOT:
      val = getModelValRec(node[0]) == d_true ? d_false : d_true;
      break;
    case kind::AND: {
      val = d_true;
      for(TNode::iterator child_it = node.begin(); child_it != node.end(); ++child_it) {
        if (getModelValRec(*child_it) != d_true) {
          val = d_false;
          break;
        }
      }
      break;
    }
    case kind::IMPLIES:
      if (getModelValRec(node[0]) == d_false) {
        val = d_true;
      }
      else {
        val = getModelValRec(node[1]);
      }
    case kind::EQUAL:
      val = getModelValRec(node[0]);
      val = (val == getModelValRec(node[1])) ? d_true : d_false;
      break;
    case kind::SELECT: {
      NodeManager* nm = NodeManager::currentNM();
      Node indexVal = getModelValRec(node[1]);
      val = Rewriter::rewrite(nm->mkNode(kind::SELECT, node[0], indexVal));
      if (val.isConst()) {
        break;
      }
      val = Rewriter::rewrite(nm->mkNode(kind::SELECT, getModelValRec(node[0]), indexVal));
      Assert(val.isConst());
      break;
    }
    case kind::STORE: {
      NodeManager* nm = NodeManager::currentNM();
      val = getModelValRec(node[0]);
      val = Rewriter::rewrite(nm->mkNode(kind::STORE, val, getModelValRec(node[1]), getModelValRec(node[2])));
      Assert(val.isConst());
      break;
    }
    default: {
      Assert(isLeaf(node));
      TNode eRep = d_equalityEngine.getRepresentative(node);
      if (eRep.isConst()) {
        val = eRep;
        break;
      }
      TNode rep = d_infoMap.getModelRep(eRep);
      if (!rep.isNull()) {
        // TODO: check for loop here
        val = getModelValRec(rep);
      }
      else {
        NodeMap::iterator it = d_lastVal.find(eRep);
        if (it != d_lastVal.end()) {
          val = (*it).second;
          if (!d_equalityEngine.hasTerm(val) ||
              !d_equalityEngine.areDisequal(eRep, val, true)) {
            getSatContext()->push();
            ++d_numGetModelValSplits;
            d_equalityEngine.assertEquality(eRep.eqNode(val), true, d_true);
            if (!d_conflict) {
              break;
            }
            ++d_numGetModelValConflicts;
            getSatContext()->pop();
          }
        }

        TypeEnumerator te(eRep.getType());
        val = *te;
        while (true) {
          if (!d_equalityEngine.hasTerm(val) ||
              !d_equalityEngine.areDisequal(eRep, val, true)) {
            getSatContext()->push();
            ++d_numGetModelValSplits;
            d_equalityEngine.assertEquality(eRep.eqNode(val), true, d_true);
            if (!d_conflict) {
              d_lastVal[eRep] = val;
              break;
            }
            ++d_numGetModelValConflicts;
            getSatContext()->pop();
          }
          ++te;
          if (te.isFinished()) {
            Assert(false);
            // TODO: conflict
            break;
          }
          val = *te;
        }
      }
      break;
    }
  }
  d_getModelValCache[node] = val;
  return val;
}


bool TheoryArrays::hasLoop(TNode node, TNode target)
{
  if (node == target) {
    return true;
  }

  if (isLeaf(node)) {
    TNode rep = d_infoMap.getModelRep(d_equalityEngine.getRepresentative(node));
    if (!rep.isNull()) {
      return hasLoop(rep, target);
    }
    return false;
  }

  for(TNode::iterator child_it = node.begin(); child_it != node.end(); ++child_it) {
    if (hasLoop(*child_it, target)) {
      return true;
    }
  }

  return false;
}


// Return true iff it we were able to modify model so that value of node has same value as val
bool TheoryArrays::setModelVal(TNode node, TNode val, bool invert, bool explain, vector<TNode>& assumptions)
{
  Assert(!d_conflict);
  if (node == val) {
    return !invert;
  }
  if (node.isConst()) {
    if (invert) {
      return (val.isConst() && node != val);
    }
    return val == node;
  }
  switch(node.getKind()) {
    case kind::NOT:
      Assert(val == d_true || val == d_false);
      return setModelVal(node[0], val, !invert, explain, assumptions);
      break;
    case kind::AND: {
      Assert(val == d_true || val == d_false);
      if (val == d_false) {
        invert = !invert;
      }
      int i;
      for(i = node.getNumChildren()-1; i >=0; --i) {
        if (setModelVal(node[i], d_true, invert, explain, assumptions) == invert) {
          return invert;
        }
      }
      return !invert;
    }
    case kind::IMPLIES:
      Assert(val == d_true || val == d_false);
      if (val == d_false) {
        invert = !invert;
      }
      if (setModelVal(node[0], d_false, invert, explain, assumptions) == !invert) {
        return !invert;
      }
      if (setModelVal(node[1], d_true, invert, explain, assumptions) == !invert) {
        return !invert;
      }
      return invert;
    case kind::EQUAL:
      Assert(val == d_true || val == d_false);
      if (val == d_false) {
        invert = !invert;
      }
      if (node[0].isConst()) {
        return setModelVal(node[1], node[0], invert, explain, assumptions);
      }
      else {
        return setModelVal(node[0], node[1], invert, explain, assumptions);
      }
    case kind::SELECT: {
      TNode s = node[0];
      Node index = node[1];

      while (s.getKind() == kind::STORE) {
        if (setModelVal(s[1].eqNode(index), d_true, false, explain, assumptions)) {
          if (setModelVal(s[2].eqNode(val), d_true, invert, explain, assumptions)) {
            return true;
          }
          // Now try to set the indices to be disequal
          if (!setModelVal(s[1].eqNode(index), d_false, false, explain, assumptions)) {
            return false;
          }
          Unreachable();
        }
        s = s[0];
      }
      TNode rep = d_infoMap.getModelRep(d_equalityEngine.getRepresentative(s));
      NodeManager* nm = NodeManager::currentNM();
      if (!rep.isNull()) {
        // TODO: check for loop
        if (explain) {
          d_equalityEngine.explainEquality(s, rep, true, assumptions);
        }
        return setModelVal(nm->mkNode(kind::SELECT, rep, index), val, invert, explain, assumptions);
      }
      if (val.getKind() == kind::SELECT && val[0].getKind() == kind::STORE) {
        return setModelVal(val, nm->mkNode(kind::SELECT, s, index), invert, explain, assumptions);
      }

      // Solve equation for s: select(s,index) op val --> s = store(s',i',v') /\ index = i' /\ v' op val
      Node newVarArr = getSkolem(s, "array_model_arr_var_$$", s.getType(), "a new array variable from the theory of arrays", false);
      Assert(d_infoMap.getModelRep(d_equalityEngine.getRepresentative(newVarArr)).isNull());
      Node lookup;
      bool checkIndex1 = false, checkIndex2 = false, checkIndex3 = false;
      if (!isLeaf(index)) {
        index = getSkolem(index, "array_model_index_$$", index.getType(), "a new index variable from the theory of arrays");
        if (!index.getType().isArray()) {
          checkIndex1 = true;
        }
      }
      lookup = nm->mkNode(kind::SELECT, s, index);
      Node newVarVal = getSkolem(lookup, "array_model_var_$$", val.getType(), "a new value variable from the theory of arrays", false);

      Node newVarVal2;
      Node index2;
      TNode saveVal = val;
      if (val.getKind() == kind::SELECT && val[0] == s) {
        // Special case: select(s,index) = select(s,j): solution becomes s = store(store(s',j,v'),index,w') /\ v' = w'
        index2 = val[1];
        if (!isLeaf(index2)) {
          index2 = getSkolem(val, "array_model_index_$$", index2.getType(), "a new index variable from the theory of arrays");
          if (!index2.getType().isArray()) {
            checkIndex2 = true;
          }
        }
        if (invert) {
          checkIndex3 = true;
        }
        lookup = nm->mkNode(kind::SELECT, s, index2);
        newVarVal2 = getSkolem(lookup, "array_model_var_$$", val.getType(), "a new value variable from the theory of arrays", false);
        newVarArr = nm->mkNode(kind::STORE, newVarArr, index2, newVarVal2);
        preRegisterTermInternal(newVarArr);
        val = newVarVal2;
      }

      Node d = nm->mkNode(kind::STORE, newVarArr, index, newVarVal);
      preRegisterTermInternal(d);
      d = s.eqNode(d);
      Debug("arrays-model-based") << "Asserting array skolem equality " << d << endl;
      d_equalityEngine.assertEquality(d, true, d_true);
      d_skolemAssertions.push_back(d);
      d_skolemIndex = d_skolemIndex + 1;
      Assert(!d_conflict);
      if (checkIndex1) {
        if (!setModelVal(node[1], index, false, explain, assumptions)) {
          return false;
        }
      }
      if (checkIndex2) {
        if (!setModelVal(saveVal[1], index2, false, explain, assumptions)) {
          return false;
        }
      }
      if (checkIndex3) {
        if (!setModelVal(index2, index, true, explain, assumptions)) {
          return false;
        }
      }
      return setModelVal(newVarVal, val, invert, explain, assumptions);
    }
    case kind::STORE:
      if (val.getKind() != kind::STORE) {
        return setModelVal(val, node, invert, explain, assumptions);
      }
      Unreachable();
      break;
    default: {
      Assert(isLeaf(node));
      TNode rep = d_infoMap.getModelRep(d_equalityEngine.getRepresentative(node));
      if (!rep.isNull()) {
        // Assume this array equation has already been dealt with - otherwise, it shouldn't have a rep
        return true;
      }
      if (val.getKind() == kind::SELECT) {
        return setModelVal(val, node, invert, explain, assumptions);
      }
      if (d_equalityEngine.hasTerm(node) &&
          d_equalityEngine.hasTerm(val)) {
        if ((!invert && d_equalityEngine.areDisequal(node, val, true)) ||
            (invert && d_equalityEngine.areEqual(node, val))) {
          if (explain) {
            d_equalityEngine.explainEquality(node, val, invert, assumptions);
          }
          return false;
        }
        if ((!invert && d_equalityEngine.areEqual(node, val)) ||
            (invert && d_equalityEngine.areDisequal(node, val, true))) {
          return true;
        }
      }
      Node d = node.eqNode(val);
      Node r = Rewriter::rewrite(d);
      if (r.isConst()) {
        d_equalityEngine.assertEquality(d, r == d_true, d_true);
        return ((r == d_true) == (!invert));
      }
      getSatContext()->push();
      d_decisions.push_back(invert ? d.negate() : d);
      d_equalityEngine.assertEquality(d, !invert, d_decisions.back());
      Debug("arrays-model-based") << "Asserting " << d_decisions.back() << " with explanation " << d_decisions.back() << endl;
      ++d_numSetModelValSplits;
      if (d_conflict) {
        ++d_numSetModelValConflicts;
        Debug("arrays-model-based") << "...which results in a conflict!" << endl;
        d = d_decisions.back();
        unsigned sz = assumptions.size();
        convertNodeToAssumptions(d_conflictNode, assumptions, d);
        unsigned sz2 = assumptions.size();
        Assert(sz2 > sz);
        Node explanation;
        if (sz2 == sz+1) {
          explanation = assumptions[sz];
        }
        else {
          NodeBuilder<> conjunction(kind::AND);
          for (unsigned i = sz; i < sz2; ++i) {
            conjunction << assumptions[i];
          }
          explanation = conjunction;
        }
        //        assumptions.push_back(d);
        //        d_lemmas.push_back(mkAnd(assumptions, true, sz));
        // while (assumptions.size() > sz2) {
        //   assumptions.pop_back();
        // }
        getSatContext()->pop();
        d_decisions.pop_back();
        d_permRef.push_back(explanation);
        d = d.negate();
        Debug("arrays-model-based") << "Asserting learned literal2 " << d << " with explanation " << explanation << endl;
        bool eq = true;
        if (d.getKind() == kind::NOT) {
          d = d[0];
          eq = false;
        }
        d_equalityEngine.assertEquality(d, eq, explanation);
        if (d_conflict) {
          Assert(false);
        }
        return false;
      }
      return true;
    }
  }
  Unreachable();
  return false;
}


Node TheoryArrays::mkAnd(std::vector<TNode>& conjunctions, bool invert, unsigned startIndex)
{
  Assert(conjunctions.size() > 0);

  std::set<TNode> all;
  std::set<TNode> explained;

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
    else if (t.getKind() == kind::OR) {
      // Expand explanation resulting from propagating a ROW lemma
      if ((explained.find(t) == explained.end())) {
        Assert(t[1].getKind() == kind::EQUAL);
        d_equalityEngine.explainEquality(t[1][0], t[1][1], false, conjunctions);
        explained.insert(t);
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
  if (options::arraysModelBased()) return;
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
    Assert(store.getKind()==kind::STORE);
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
      lem = make_quad(store, c, j, i);
      Trace("arrays-lem") << spaces(getSatContext()->getLevel()) <<"Arrays::setNonLinear ("<<store<<", "<<c<<", "<<j<<", "<<i<<")\n";
      queueRowLemma(lem);
    }
  }

}

/*****
 * When two array equivalence classes are merged, we may need to apply RIntro1 to a store in one of the EC's
 * Here, we check the stores in a to see if any need RIntro1 applied
 * We apply RIntro1 whenever:
 * (a) a store becomes equal to another store
 * (b) a store becomes equal to any term t such that read(t,i) exists
 * (c) a store becomes equal to the root array of the store (i.e. store(store(...store(a,i,v)...)) = a)
 */
void TheoryArrays::checkRIntro1(TNode a, TNode b)
{
  const CTNodeList* astores = d_infoMap.getStores(a);
  // Apply RIntro1 if applicable
  CTNodeList::const_iterator it = astores->begin();

  if (it == astores->end()) {
    // No stores in this equivalence class - return
    return;
  }

  ++it;
  if (it != astores->end()) {
    // More than one store: should have already been applied
    Assert(d_infoMap.rIntro1Applied(*it));
    Assert(d_infoMap.rIntro1Applied(*(--it)));
    return;
  }

  // Exactly one store - see if we need to apply RIntro1
  --it;
  TNode s = *it;
  Assert(s.getKind() == kind::STORE);
  if (d_infoMap.rIntro1Applied(s)) {
    // RIntro1 already applied to s
    return;
  }

  // Should be no reads from this EC
  Assert(d_infoMap.getIndices(a)->begin() == d_infoMap.getIndices(a)->end());

  bool apply = false;
  if (d_infoMap.getStores(b)->size() > 0) {
    // Case (a): two stores become equal
    apply = true;
  }
  else {
    const CTNodeList* i_b = d_infoMap.getIndices(b);
    if (i_b->begin() != i_b->end()) {
      // Case (b): there are reads from b
      apply = true;
    }
    else {
      // Get root array of s
      TNode e1 = s[0];
      while (e1.getKind() == kind::STORE) {
        e1 = e1[0];
      }
      Assert(d_equalityEngine.hasTerm(e1));
      Assert(d_equalityEngine.hasTerm(b));
      if (d_equalityEngine.areEqual(e1, b)) {
        apply = true;
      }
    }
  }

  if (apply) {
    NodeManager* nm = NodeManager::currentNM();
    d_infoMap.setRIntro1Applied(s);
    Node ni = nm->mkNode(kind::SELECT, s, s[1]);
    preRegisterTermInternal(ni);
    d_equalityEngine.assertEquality(ni.eqNode(s[2]), true, d_true);
  }
}


Node TheoryArrays::removeRepLoops(TNode a, TNode rep)
{
  if (rep.getKind() != kind::STORE) {
    Assert(isLeaf(rep));
    TNode tmp = d_infoMap.getModelRep(d_equalityEngine.getRepresentative(rep));
    if (!tmp.isNull()) {
      Node tmp2 = removeRepLoops(a, tmp);
      if (tmp != tmp2) {
        return tmp2;
      }
    }
    return rep;
  }

  Node s = removeRepLoops(a, rep[0]);
  bool changed = (s != rep[0]);

  Node index = rep[1];
  Node value = rep[2];
  Node lookup;

  // TODO: Change to hasLoop?
  if (!isLeaf(index)) {
    changed = true;
    index = getSkolem(index, "array_model_index_$$", index.getType(), "a new index variable from the theory of arrays", false);
    if (!d_equalityEngine.hasTerm(index) ||
        !d_equalityEngine.hasTerm(rep[1]) ||
        !d_equalityEngine.areEqual(rep[1], index)) {
      Node d = index.eqNode(rep[1]);
      Debug("arrays-model-based") << "Asserting skolem equality " << d << endl;
      d_equalityEngine.assertEquality(d, true, d_true);
      d_modelConstraints.push_back(d);
    }
  }
  if (!isLeaf(value)) {
    changed = true;
    value = getSkolem(value, "array_model_var_$$", value.getType(), "a new value variable from the theory of arrays", false);
    if (!d_equalityEngine.hasTerm(value) ||
        !d_equalityEngine.hasTerm(rep[2]) ||
        !d_equalityEngine.areEqual(rep[2], value)) {
      Node d = value.eqNode(rep[2]);
      Debug("arrays-model-based") << "Asserting skolem equality " << d << endl;
      d_equalityEngine.assertEquality(d, true, d_true);
      d_modelConstraints.push_back(d);
    }
  }
  if (changed) {
    NodeManager* nm = NodeManager::currentNM();
    return nm->mkNode(kind::STORE, s, index, value);
  }
  return rep;
}


Node TheoryArrays::expandStores(TNode s, vector<TNode>& assumptions, bool checkLoop, TNode a, TNode loopRep)
{
  if (s.getKind() != kind::STORE) {
    Assert(isLeaf(s));
    TNode tmp = d_equalityEngine.getRepresentative(s);
    if (checkLoop && tmp == a) {
      // Loop detected
      d_equalityEngine.explainEquality(s, loopRep, true, assumptions);
      return loopRep;
    }
    tmp = d_infoMap.getModelRep(tmp);
    if (!tmp.isNull()) {
      d_equalityEngine.explainEquality(s, tmp, true, assumptions);
      return expandStores(tmp, assumptions, checkLoop, a, loopRep);
    }
    return s;
  }
  Node tmp = expandStores(s[0], assumptions, checkLoop, a, loopRep);
  if (tmp != s[0]) {
    NodeManager* nm = NodeManager::currentNM();
    return nm->mkNode(kind::STORE, tmp, s[1], s[2]);
  }
  return s;
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
    Trace("arrays-merge") << spaces(getSatContext()->getLevel()) << "Arrays::merge: " << a << "," << b << ")\n";

    if (options::arraysLazyRIntro1()) {
      checkRIntro1(a, b);
      checkRIntro1(b, a);
    }

    if (options::arraysOptimizeLinear() && !options::arraysModelBased()) {
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

    d_mayEqualEqualityEngine.assertEquality(a.eqNode(b), true, d_true);

    checkRowLemmas(a,b);
    checkRowLemmas(b,a);

    if (options::arraysModelBased()) {
      TNode repA = d_infoMap.getModelRep(a);
      Assert(repA.isNull() || d_equalityEngine.areEqual(a, repA));
      TNode repB = d_infoMap.getModelRep(b);
      Assert(repB.isNull() || d_equalityEngine.areEqual(a, repB));
      Node rep;
      bool done = false;
      if (repA.isNull()) {
        if (repB.isNull()) {
          done = true;
        }
        else {
          rep = repB;
        }
      }
      else {
        if (repB.isNull()) {
          rep = repA;
        }
        else {
          vector<TNode> assumptions;
          rep = expandStores(repA, assumptions, true, a, repB);
          if (rep != repA) {
            Debug("arrays-model-based") << "Merging (" << a << "," << b << "): new rep is " << rep << endl;
            d_infoMap.setModelRep(a, rep);
            Node reason = mkAnd(assumptions);
            d_permRef.push_back(reason);
            d_equalityEngine.assertEquality(repA.eqNode(rep), true, reason);
          }
          d_modelConstraints.push_back(rep.eqNode(repB));
          done = true;
        }
      }
      if (!done) {
        // 1. Check for store loop
        TNode s = rep;
        while (true) {
          Assert(s.getKind() == kind::STORE);
          while (s.getKind() == kind::STORE) {
            s = s[0];
          }
          Assert(isLeaf(s));
          TNode tmp = d_equalityEngine.getRepresentative(s);
          if (tmp == a) {
            d_modelConstraints.push_back(s.eqNode(rep));
            rep = TNode();
            break;
          }
          tmp = d_infoMap.getModelRep(tmp);
          if (tmp.isNull()) {
            break;
          }
          s = tmp;
        }
        if (!rep.isNull()) {
          Node repOrig = rep;
          rep = removeRepLoops(a, rep);
          if (repOrig != rep) {
            d_equalityEngine.assertEquality(repOrig.eqNode(rep), true, d_true);
          }
        }
        if (rep != repA) {
          Debug("arrays-model-based") << "Merging (" << a << "," << b << "): new rep is " << rep << endl;
          d_infoMap.setModelRep(a, rep);
        }
      }
    }

    // merge info adds the list of the 2nd argument to the first
    d_infoMap.mergeInfo(a, b);

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
  if (options::arraysModelBased()) return;
  Trace("arrays-cri")<<"Arrays::checkStore "<<a<<"\n";

  if(Trace.isOn("arrays-cri")) {
    d_infoMap.getInfo(a)->print();
  }
  Assert(a.getType().isArray());
  Assert(a.getKind()==kind::STORE);
  TNode b = a[0];
  TNode i = a[1];

  TNode brep = d_equalityEngine.getRepresentative(b);

  if (!options::arraysOptimizeLinear() || d_infoMap.isNonLinear(brep)) {
    const CTNodeList* js = d_infoMap.getIndices(brep);
    size_t it = 0;
    RowLemmaType lem;
    for(; it < js->size(); ++it) {
      TNode j = (*js)[it];
      if (i == j) continue;
      lem = make_quad(a,b,i,j);
      Trace("arrays-lem") << spaces(getSatContext()->getLevel()) <<"Arrays::checkStore ("<<a<<", "<<b<<", "<<i<<", "<<j<<")\n";
      queueRowLemma(lem);
    }
  }
}


void TheoryArrays::checkRowForIndex(TNode i, TNode a)
{
  if (options::arraysModelBased()) return;
  Trace("arrays-cri")<<"Arrays::checkRowForIndex "<<a<<"\n";
  Trace("arrays-cri")<<"                   index "<<i<<"\n";

  if(Trace.isOn("arrays-cri")) {
    d_infoMap.getInfo(a)->print();
  }
  Assert(a.getType().isArray());
  Assert(d_equalityEngine.getRepresentative(a) == a);

  const CTNodeList* stores = d_infoMap.getStores(a);
  const CTNodeList* instores = d_infoMap.getInStores(a);
  size_t it = 0;
  RowLemmaType lem;

  for(; it < stores->size(); ++it) {
    TNode store = (*stores)[it];
    Assert(store.getKind()==kind::STORE);
    TNode j = store[1];
    if (i == j) continue;
    lem = make_quad(store, store[0], j, i);
    Trace("arrays-lem") << spaces(getSatContext()->getLevel()) <<"Arrays::checkRowForIndex ("<<store<<", "<<store[0]<<", "<<j<<", "<<i<<")\n";
    queueRowLemma(lem);
  }

  if (!options::arraysOptimizeLinear() || d_infoMap.isNonLinear(a)) {
    it = 0;
    for(; it < instores->size(); ++it) {
      TNode instore = (*instores)[it];
      Assert(instore.getKind()==kind::STORE);
      TNode j = instore[1];
      if (i == j) continue;
      lem = make_quad(instore, instore[0], j, i);
      Trace("arrays-lem") << spaces(getSatContext()->getLevel()) <<"Arrays::checkRowForIndex ("<<instore<<", "<<instore[0]<<", "<<j<<", "<<i<<")\n";
      queueRowLemma(lem);
    }
  }
}


// a just became equal to b
// look for new ROW lemmas
void TheoryArrays::checkRowLemmas(TNode a, TNode b)
{
  if (options::arraysModelBased()) return;
  Trace("arrays-crl")<<"Arrays::checkLemmas begin \n"<<a<<"\n";
  if(Trace.isOn("arrays-crl"))
    d_infoMap.getInfo(a)->print();
  Trace("arrays-crl")<<"  ------------  and "<<b<<"\n";
  if(Trace.isOn("arrays-crl"))
    d_infoMap.getInfo(b)->print();

  const CTNodeList* i_a = d_infoMap.getIndices(a);
  const CTNodeList* st_b = d_infoMap.getStores(b);
  const CTNodeList* inst_b = d_infoMap.getInStores(b);

  size_t it = 0;
  size_t its;

  RowLemmaType lem;

  for( ; it < i_a->size(); ++it) {
    TNode i = (*i_a)[it];
    its = 0;
    for ( ; its < st_b->size(); ++its) {
      TNode store = (*st_b)[its];
      Assert(store.getKind() == kind::STORE);
      TNode j = store[1];
      TNode c = store[0];
      lem = make_quad(store, c, j, i);
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
        lem = make_quad(store, c, j, i);
        Trace("arrays-lem") << spaces(getSatContext()->getLevel()) <<"Arrays::checkRowLemmas ("<<store<<", "<<c<<", "<<j<<", "<<i<<")\n";
        queueRowLemma(lem);
      }
    }
  }
  Trace("arrays-crl")<<"Arrays::checkLemmas done.\n";
}

void TheoryArrays::queueRowLemma(RowLemmaType lem)
{
  if (d_conflict || d_RowAlreadyAdded.contains(lem)) {
    return;
  }
  TNode a = lem.first;
  TNode b = lem.second;
  TNode i = lem.third;
  TNode j = lem.fourth;

  Assert(a.getType().isArray() && b.getType().isArray());
  if (d_equalityEngine.areEqual(a,b) ||
      d_equalityEngine.areEqual(i,j)) {
    return;
  }

  NodeManager* nm = NodeManager::currentNM();
  Node aj = nm->mkNode(kind::SELECT, a, j);
  Node bj = nm->mkNode(kind::SELECT, b, j);

  // Try to avoid introducing new read terms: track whether these already exist
  bool ajExists = d_equalityEngine.hasTerm(aj);
  bool bjExists = d_equalityEngine.hasTerm(bj);
  bool bothExist = ajExists && bjExists;

  // If propagating, check propagations
  if (d_propagateLemmas) {
    if (d_equalityEngine.areDisequal(i,j,true)) {
      Trace("arrays-lem") << spaces(getSatContext()->getLevel()) <<"Arrays::queueRowLemma: propagating aj = bj ("<<aj<<", "<<bj<<")\n";
      Node aj_eq_bj = aj.eqNode(bj);
      Node i_eq_j = i.eqNode(j);
      Node reason = nm->mkNode(kind::OR, aj_eq_bj, i_eq_j);
      d_permRef.push_back(reason);
      if (!ajExists) {
        preRegisterTermInternal(aj);
      }
      if (!bjExists) {
        preRegisterTermInternal(bj);
      }
      d_equalityEngine.assertEquality(aj_eq_bj, true, reason);
      ++d_numProp;
      return;
    }
    if (bothExist && d_equalityEngine.areDisequal(aj,bj,true)) {
      Trace("arrays-lem") << spaces(getSatContext()->getLevel()) <<"Arrays::queueRowLemma: propagating i = j ("<<i<<", "<<j<<")\n";
      Node aj_eq_bj = aj.eqNode(bj);
      Node i_eq_j = i.eqNode(j);
      Node reason = nm->mkNode(kind::OR, i_eq_j, aj_eq_bj);
      d_permRef.push_back(reason);
      d_equalityEngine.assertEquality(i_eq_j, true, reason);
      ++d_numProp;
      return;
    }
  }

  // If equivalent lemma already exists, don't enqueue this one
  if (d_useArrTable) {
    Node tableEntry = NodeManager::currentNM()->mkNode(kind::ARR_TABLE_FUN, a, b, i, j);
    if (d_equalityEngine.getSize(tableEntry) != 1) {
      return;
    }
  }

  // Prefer equality between indexes so as not to introduce new read terms
  if (options::arraysEagerIndexSplitting() && !bothExist && !d_equalityEngine.areDisequal(i,j, false)) {
    Node i_eq_j = d_valuation.ensureLiteral(i.eqNode(j));
    getOutputChannel().requirePhase(i_eq_j, true);
    d_decisionRequests.push(i_eq_j);
  }

  // TODO: maybe add triggers here

  if (options::arraysEagerLemmas() || bothExist) {

    // Make sure that any terms introduced by rewriting are appropriately stored in the equality database
    Node aj2 = Rewriter::rewrite(aj);
    if (aj != aj2) {
      if (!ajExists) {
        preRegisterTermInternal(aj);
      }
      if (!d_equalityEngine.hasTerm(aj2)) {
        preRegisterTermInternal(aj2);
      }
      d_equalityEngine.assertEquality(aj.eqNode(aj2), true, d_true);
    }
    Node bj2 = Rewriter::rewrite(bj);
    if (bj != bj2) {
      if (!bjExists) {
        preRegisterTermInternal(bj);
      }
      if (!d_equalityEngine.hasTerm(bj2)) {
        preRegisterTermInternal(bj2);
      }
      d_equalityEngine.assertEquality(bj.eqNode(bj2), true, d_true);
    }
    if (aj2 == bj2) {
      return;
    }

    // construct lemma
    Node eq1 = aj2.eqNode(bj2);
    Node eq1_r = Rewriter::rewrite(eq1);
    if (eq1_r == d_true) {
      if (!d_equalityEngine.hasTerm(aj2)) {
        preRegisterTermInternal(aj2);
      }
      if (!d_equalityEngine.hasTerm(bj2)) {
        preRegisterTermInternal(bj2);
      }
      d_equalityEngine.assertEquality(eq1, true, d_true);
      return;
    }

    Node eq2 = i.eqNode(j);
    Node eq2_r = Rewriter::rewrite(eq2);
    if (eq2_r == d_true) {
      d_equalityEngine.assertEquality(eq2, true, d_true);
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


Node TheoryArrays::getNextDecisionRequest() {
  if(! d_decisionRequests.empty()) {
    Node n = d_decisionRequests.front();
    d_decisionRequests.pop();
    return n;
  } else {
    return Node::null();
  }
}


void TheoryArrays::dischargeLemmas()
{
  size_t sz = d_RowQueue.size();
  for (unsigned count = 0; count < sz; ++count) {
    RowLemmaType l = d_RowQueue.front();
    d_RowQueue.pop();
    if (d_RowAlreadyAdded.contains(l)) {
      continue;
    }

    TNode a = l.first;
    TNode b = l.second;
    TNode i = l.third;
    TNode j = l.fourth;
    Assert(a.getType().isArray() && b.getType().isArray());

    NodeManager* nm = NodeManager::currentNM();
    Node aj = nm->mkNode(kind::SELECT, a, j);
    Node bj = nm->mkNode(kind::SELECT, b, j);
    bool ajExists = d_equalityEngine.hasTerm(aj);
    bool bjExists = d_equalityEngine.hasTerm(bj);

    // Check for redundant lemma
    // TODO: more checks possible (i.e. check d_RowAlreadyAdded in context)
    if (!d_equalityEngine.hasTerm(i) || !d_equalityEngine.hasTerm(j) || d_equalityEngine.areEqual(i,j) ||
        !d_equalityEngine.hasTerm(a) || !d_equalityEngine.hasTerm(b) || d_equalityEngine.areEqual(a,b) ||
        (ajExists && bjExists && d_equalityEngine.areEqual(aj,bj))) {
      continue;
    }

    // Make sure that any terms introduced by rewriting are appropriately stored in the equality database
    Node aj2 = Rewriter::rewrite(aj);
    if (aj != aj2) {
      if (!ajExists) {
        preRegisterTermInternal(aj);
      }
      if (!d_equalityEngine.hasTerm(aj2)) {
        preRegisterTermInternal(aj2);
      }
      d_equalityEngine.assertEquality(aj.eqNode(aj2), true, d_true);
    }
    Node bj2 = Rewriter::rewrite(bj);
    if (bj != bj2) {
      if (!bjExists) {
        preRegisterTermInternal(bj);
      }
      if (!d_equalityEngine.hasTerm(bj2)) {
        preRegisterTermInternal(bj2);
      }
      d_equalityEngine.assertEquality(bj.eqNode(bj2), true, d_true);
    }
    if (aj2 == bj2) {
      continue;
    }

    // construct lemma
    Node eq1 = aj2.eqNode(bj2);
    Node eq1_r = Rewriter::rewrite(eq1);
    if (eq1_r == d_true) {
      if (!d_equalityEngine.hasTerm(aj2)) {
        preRegisterTermInternal(aj2);
      }
      if (!d_equalityEngine.hasTerm(bj2)) {
        preRegisterTermInternal(bj2);
      }
      d_equalityEngine.assertEquality(eq1, true, d_true);
      continue;
    }

    Node eq2 = i.eqNode(j);
    Node eq2_r = Rewriter::rewrite(eq2);
    if (eq2_r == d_true) {
      d_equalityEngine.assertEquality(eq2, true, d_true);
      continue;
    }

    Node lem = nm->mkNode(kind::OR, eq2_r, eq1_r);

    Trace("arrays-lem")<<"Arrays::addRowLemma adding "<<lem<<"\n";
    d_RowAlreadyAdded.insert(l);
    d_out->lemma(lem);
    ++d_numRow;
  }
}

void TheoryArrays::conflict(TNode a, TNode b) {
  if (a.getKind() == kind::CONST_BOOLEAN) {
    d_conflictNode = explain(a.iffNode(b));
  } else {
    d_conflictNode = explain(a.eqNode(b));
  }
  if (!d_inCheckModel) {
    d_out->conflict(d_conflictNode);
  }
  d_conflict = true;
}


}/* CVC4::theory::arrays namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */
