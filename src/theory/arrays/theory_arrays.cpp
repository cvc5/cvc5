/*********************                                                        */
/*! \file theory_arrays.cpp
 ** \verbatim
 ** Original author: barrett
 ** Major contributors: mdeters
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010, 2011  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
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
const bool d_eagerLemmas = false;
const bool d_propagateLemmas = true;
const bool d_preprocess = true;
const bool d_solveWrite = true;
const bool d_solveWrite2 = false;
const bool d_useNonLinearOpt = true;
const bool d_eagerIndexSplitting = true;

TheoryArrays::TheoryArrays(context::Context* c, context::UserContext* u, OutputChannel& out, Valuation valuation, const LogicInfo& logicInfo) :
  Theory(THEORY_ARRAY, c, u, out, valuation, logicInfo),
  d_numRow("theory::arrays::number of Row lemmas", 0),
  d_numExt("theory::arrays::number of Ext lemmas", 0),
  d_numProp("theory::arrays::number of propagations", 0),
  d_numExplain("theory::arrays::number of explanations", 0),
  d_numNonLinear("theory::arrays::number of calls to setNonLinear", 0),
  d_numSharedArrayVarSplits("theory::arrays::number of shared array var splits", 0),
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
  d_RowQueue(u),
  d_RowAlreadyAdded(u),
  d_sharedArrays(c),
  d_sharedTerms(c, false),
  d_reads(c),
  d_permRef(c)
{
  StatisticsRegistry::registerStat(&d_numRow);
  StatisticsRegistry::registerStat(&d_numExt);
  StatisticsRegistry::registerStat(&d_numProp);
  StatisticsRegistry::registerStat(&d_numExplain);
  StatisticsRegistry::registerStat(&d_numNonLinear);
  StatisticsRegistry::registerStat(&d_numSharedArrayVarSplits);
  StatisticsRegistry::registerStat(&d_checkTimer);

  d_true = NodeManager::currentNM()->mkConst<bool>(true);
  d_false = NodeManager::currentNM()->mkConst<bool>(false);

  // The kinds we are treating as function application in congruence
  d_equalityEngine.addFunctionKind(kind::SELECT);
  if (d_ccStore) {
    d_equalityEngine.addFunctionKind(kind::STORE);
  }
  d_equalityEngine.addFunctionKind(kind::EQUAL);
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
  StatisticsRegistry::unregisterStat(&d_checkTimer);

}


/////////////////////////////////////////////////////////////////////////////
// PREPROCESSING
/////////////////////////////////////////////////////////////////////////////


Node TheoryArrays::ppRewrite(TNode term) {
  if (!d_preprocess) return term;
  switch (term.getKind()) {
    case kind::SELECT: {
      // select(store(a,i,v),j) = select(a,j)
      //    IF i != j
      if (term[0].getKind() == kind::STORE &&
          (d_ppEqualityEngine.areDisequal(term[0][1], term[1]) ||
           (term[0][1].isConst() && term[1].isConst() && term[0][1] != term[1]))) {
        return NodeBuilder<2>(kind::SELECT) << term[0][0] << term[1];
      }
      break;
    }
    case kind::STORE: {
      // store(store(a,i,v),j,w) = store(store(a,j,w),i,v)
      //    IF i != j and j comes before i in the ordering
      if (term[0].getKind() == kind::STORE &&
          (term[1] < term[0][1]) &&
          (d_ppEqualityEngine.areDisequal(term[1], term[0][1]) ||
           (term[0][1].isConst() && term[1].isConst() && term[0][1] != term[1]))) {
        Node inner = NodeBuilder<3>(kind::STORE) << term[0][0] << term[1] << term[2];
        Node outer = NodeBuilder<3>(kind::STORE) << inner << term[0][1] << term[0][2];
        return outer;
      }
      break;
    }
    case kind::EQUAL: {
      if (!d_solveWrite) break;
      if (term[0].getKind() == kind::STORE ||
          term[1].getKind() == kind::STORE) {
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
          if (e1 == e2) {
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
                  if (d_ppEqualityEngine.areDisequal(index_i, index_j) ||
                      (index_i.isConst() && index_j.isConst() && index_i != index_j)) {
                    continue;
                  }
                  Node hyp2(index_i.getType() == nm->booleanType()? 
                            index_i.iffNode(index_j) : index_i.eqNode(index_j));
                  hyp << hyp2.notNode();
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
          break;
        }
        else {
          if (!d_solveWrite2) break;
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
          nb << l.eqNode(right);
          return nb;
        }
      }
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
      if (in[0].getMetaKind() == kind::metakind::VARIABLE && !in[1].hasSubterm(in[0])) {
        outSubstitutions.addSubstitution(in[0], in[1]);
        return PP_ASSERT_STATUS_SOLVED;
      }
      if (in[1].getMetaKind() == kind::metakind::VARIABLE && !in[0].hasSubterm(in[1])) {
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

  // See if the literal has been asserted already
  Node normalized = Rewriter::rewrite(literal);
  bool satValue = false;
  bool isAsserted = normalized == d_false || d_valuation.hasSatValue(normalized, satValue);

  // If asserted, we're done or in conflict
  if (isAsserted) {
    if (!satValue) {
      Debug("arrays") << spaces(getSatContext()->getLevel()) << "TheoryArrays::propagate(" << literal << ", normalized = " << normalized << ") => conflict" << std::endl;
      std::vector<TNode> assumptions;
      Node negatedLiteral;
      negatedLiteral = normalized.getKind() == kind::NOT ? (Node) normalized[0] : normalized.notNode();
      assumptions.push_back(negatedLiteral);
      explain(literal, assumptions);
      d_conflictNode = mkAnd(assumptions);
      d_conflict = true;
      return false;
    }
    // Propagate even if already known in SAT - could be a new equation between shared terms
    // (terms that weren't shared when the literal was asserted!)
  }

  // Nothing, just enqueue it for propagation and mark it as asserted already
  Debug("arrays") << spaces(getSatContext()->getLevel()) << "TheoryArrays::propagate(" << literal << ") => enqueuing for propagation" << std::endl;
  d_literalsToPropagate.push_back(literal);

  return true;
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
void TheoryArrays::preRegisterTerm(TNode node)
{
  Debug("arrays") << spaces(getSatContext()->getLevel()) << "TheoryArrays::preRegisterTerm(" << node << ")" << std::endl;
  switch (node.getKind()) {
  case kind::EQUAL:
    // Add the trigger for equality
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
          preRegisterTerm(ni);
        }
        d_equalityEngine.assertEquality(ni.eqNode(s[2]), true, d_true);
        Assert(++it == stores->end());
      }
    }

    d_equalityEngine.addTerm(node);
    // Maybe it's a predicate
    // TODO: remove this or keep it if we allow Boolean elements in arrays.
    if (node.getType().isBoolean()) {
      // Get triggered for both equal and dis-equal
      d_equalityEngine.addTriggerPredicate(node);
    }

    d_infoMap.addIndex(node[0], node[1]);
    d_reads.push_back(node);
    Assert((d_isPreRegistered.insert(node), true));
    checkRowForIndex(node[1], store);
    break;
  }
  case kind::STORE: {
    // Invariant: array terms should be preregistered before being added to the equality engine
    Assert(!d_equalityEngine.hasTerm(node));
    d_equalityEngine.addTriggerTerm(node);

    TNode a = node[0];
    //    TNode i = node[1];
    //    TNode v = node[2];

    d_mayEqualEqualityEngine.assertEquality(node.eqNode(a), true, d_true);

    // NodeManager* nm = NodeManager::currentNM();
    // Node ni = nm->mkNode(kind::SELECT, node, i);
    // if (!d_equalityEngine.hasTerm(ni)) {
    //   preRegisterTerm(ni);
    // }

    // // Apply RIntro1 Rule
    // d_equalityEngine.addEquality(ni, v, d_true);

    d_infoMap.addStore(node, node);
    d_infoMap.addInStore(a, node);

    checkStore(node);
    break;
  }
  default:
    // Variables etc
    if (node.getType().isArray()) {
      d_equalityEngine.addTriggerTerm(node);
      Assert(d_equalityEngine.getSize(node) == 1);
    }
    else {
      d_equalityEngine.addTerm(node);
    }
    break;
  }
  // Invariant: preregistered terms are exactly the terms in the equality engine
  Assert(d_equalityEngine.hasTerm(node));
}


void TheoryArrays::propagate(Effort e)
{
  Debug("arrays") << spaces(getSatContext()->getLevel()) << "TheoryArrays::propagate()" << std::endl;
  if (!d_conflict) {
    for (; d_literalsToPropagateIndex < d_literalsToPropagate.size(); d_literalsToPropagateIndex = d_literalsToPropagateIndex + 1) {
      TNode literal = d_literalsToPropagate[d_literalsToPropagateIndex];
      Debug("arrays") << spaces(getSatContext()->getLevel()) << "TheoryArrays::propagate(): propagating " << literal << std::endl;
      bool satValue;
      Node normalized = Rewriter::rewrite(literal);
      if (!d_valuation.hasSatValue(normalized, satValue) || satValue) {
        d_out->propagate(literal);
      } else {
        Debug("arrays") << spaces(getSatContext()->getLevel()) << "TheoryArrays::propagate(): in conflict, normalized = " << normalized << std::endl;
        Node negatedLiteral;
        std::vector<TNode> assumptions;
        negatedLiteral = normalized.getKind() == kind::NOT ? (Node) normalized[0] : normalized.notNode();
        assumptions.push_back(negatedLiteral);
        explain(literal, assumptions);
        d_conflictNode = mkAnd(assumptions);
        d_conflict = true;
        break;
      }
    }
  }

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
  d_equalityEngine.addTriggerTerm(t);
  if (t.getType().isArray()) {
    d_sharedArrays.insert(t,true);
  }
  else {
    d_sharedTerms = true;
  }
}


EqualityStatus TheoryArrays::getEqualityStatus(TNode a, TNode b) {
  Assert(d_equalityEngine.hasTerm(a) && d_equalityEngine.hasTerm(b));
  if (d_equalityEngine.areEqual(a, b)) {
    // The terms are implied to be equal
    return EQUALITY_TRUE;
  }
  if (d_equalityEngine.areDisequal(a, b)) {
    // The terms are implied to be dis-equal
    return EQUALITY_FALSE;
  }
  //TODO: can we be more precise sometimes?
  return EQUALITY_UNKNOWN;
}


void TheoryArrays::computeCareGraph()
{
  if (d_sharedArrays.size() > 0) {
    context::CDHashMap<TNode, bool, TNodeHashFunction>::iterator it1 = d_sharedArrays.begin(), it2, iend = d_sharedArrays.end();
    for (; it1 != iend; ++it1) {
      for (it2 = it1, ++it2; it2 != iend; ++it2) {
        if ((*it1).first.getType() != (*it2).first.getType()) {
          continue;
        }
        EqualityStatus eqStatusArr = getEqualityStatus((*it1).first, (*it2).first);
        if (eqStatusArr != EQUALITY_UNKNOWN) {
          continue;
        }
        Assert(d_valuation.getEqualityStatus((*it1).first, (*it2).first) == EQUALITY_UNKNOWN);
        addCarePair((*it1).first, (*it2).first);
        ++d_numSharedArrayVarSplits;
        return;
      }
    }
  }
  if (d_sharedTerms) {

    vector< pair<TNode, TNode> > currentPairs;

    // Go through the read terms and see if there are any to split on
    unsigned size = d_reads.size();
    for (unsigned i = 0; i < size; ++ i) {
      TNode r1 = d_reads[i];

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
          Assert(d_equalityEngine.hasTerm(r1[0]) && d_equalityEngine.hasTerm(r2[0]));
          if (r1[0].getType() != r2[0].getType() ||
              (!d_mayEqualEqualityEngine.areEqual(r1[0], r2[0])) ||
              d_equalityEngine.areDisequal(r1[0], r2[0])) {
            Debug("arrays::sharing") << "TheoryArrays::computeCareGraph(): arrays can't be equal, skipping" << std::endl;
            continue;
          }
        }

        TNode x = r1[1];
        TNode y = r2[1];

        if (!d_equalityEngine.isTriggerTerm(x) || !d_equalityEngine.isTriggerTerm(y)) {
          Debug("arrays::sharing") << "TheoryArrays::computeCareGraph(): not connected to shared terms, skipping" << std::endl;
          continue;
        }

        EqualityStatus eqStatus = getEqualityStatus(x, y);

        if (eqStatus != EQUALITY_UNKNOWN) {
          Debug("arrays::sharing") << "TheoryArrays::computeCareGraph(): equality status known, skipping" << std::endl;
          continue;
        }

        // Get representative trigger terms
        TNode x_shared = d_equalityEngine.getTriggerTermRepresentative(x);
        TNode y_shared = d_equalityEngine.getTriggerTermRepresentative(y);

        EqualityStatus eqStatusDomain = d_valuation.getEqualityStatus(x_shared, y_shared);
        switch (eqStatusDomain) {
          case EQUALITY_TRUE_AND_PROPAGATED:
            // Should have been propagated to us
            Assert(false);
            break;
          case EQUALITY_FALSE_AND_PROPAGATED:
            // TODO: eventually this should be an Assert(false), but for now, disequalities are not propagated
            continue;
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


Node TheoryArrays::getValue(TNode n)
{
  // TODO: Implement this
  NodeManager* nodeManager = NodeManager::currentNM();

  switch(n.getKind()) {

  case kind::VARIABLE:
    Unhandled(kind::VARIABLE);

  case kind::EQUAL: // 2 args
    return nodeManager->
      mkConst( d_valuation.getValue(n[0]) == d_valuation.getValue(n[1]) );

  default:
    Unhandled(n.getKind());
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


void TheoryArrays::check(Effort e) {
  TimerStat::CodeTimer codeTimer(d_checkTimer);

  while (!done() && !d_conflict) 
  {
    // Get all the assertions
    Assertion assertion = get();
    TNode fact = assertion.assertion;

    Debug("arrays") << spaces(getSatContext()->getLevel()) << "TheoryArrays::check(): processing " << fact << std::endl;

    // If the assertion doesn't have a literal, it's a shared equality
    Assert(assertion.isPreregistered ||
           ((fact.getKind() == kind::EQUAL && d_equalityEngine.hasTerm(fact[0]) && d_equalityEngine.hasTerm(fact[1])) ||
            (fact.getKind() == kind::NOT && fact[0].getKind() == kind::EQUAL &&
             d_equalityEngine.hasTerm(fact[0][0]) && d_equalityEngine.hasTerm(fact[0][1]))));

    // Do the work
    switch (fact.getKind()) {
      case kind::EQUAL:
        d_equalityEngine.assertEquality(fact, true, fact);
        break;
      case kind::SELECT:
        d_equalityEngine.assertPredicate(fact, true, fact);
        break;
      case kind::NOT:
        if (fact[0].getKind() == kind::SELECT) {
          d_equalityEngine.assertPredicate(fact[0], false, fact);
        } else if (!d_equalityEngine.areDisequal(fact[0][0], fact[0][1])) {
          // Assert the dis-equality
          d_equalityEngine.assertEquality(fact[0], false, fact);

          // Apply ArrDiseq Rule if diseq is between arrays
          if(fact[0][0].getType().isArray()) {
            NodeManager* nm = NodeManager::currentNM();
            TypeNode indexType = fact[0][0].getType()[0];
            TNode k;
            std::hash_map<TNode, Node, TNodeHashFunction>::iterator it = d_diseqCache.find(fact);
            if (it == d_diseqCache.end()) {
              Node newk = nm->mkVar(indexType);
	      Dump.declareVar(newk.toExpr(),
                              "an extensional lemma index variable from the theory of arrays");
              d_diseqCache[fact] = newk;
              k = newk;
            }
            else {
              k = (*it).second;
            }

            Node ak = nm->mkNode(kind::SELECT, fact[0][0], k);
            Node bk = nm->mkNode(kind::SELECT, fact[0][1], k);
            if (!d_equalityEngine.hasTerm(ak)) {
              preRegisterTerm(ak);
            }
            if (!d_equalityEngine.hasTerm(bk)) {
              preRegisterTerm(bk);
            }
            d_equalityEngine.assertEquality(ak.eqNode(bk), false, fact);
            Trace("arrays-lem")<<"Arrays::addExtLemma "<< ak << " /= " << bk <<"\n";
            ++d_numExt;
          }
        }
        break;
      default:
        Unreachable();
    }
  }

  // If in conflict, output the conflict
  if (d_conflict) {
    Debug("arrays") << spaces(getSatContext()->getLevel()) << "TheoryArrays::check(): conflict " << d_conflictNode << std::endl;
    d_out->conflict(d_conflictNode);
  }
  else {
    // Otherwise we propagate
    propagate(e);

    if(!d_eagerLemmas && fullEffort(e)) {
      // generate the lemmas on the worklist
      Trace("arrays-lem")<<"Arrays::discharging lemmas: "<<d_RowQueue.size()<<"\n";
      dischargeLemmas();
    }
  }

  Trace("arrays") << spaces(getSatContext()->getLevel()) << "Arrays::check(): done" << endl;
}


Node TheoryArrays::mkAnd(std::vector<TNode>& conjunctions)
{
  Assert(conjunctions.size() > 0);

  std::set<TNode> all;
  std::set<TNode> explained;

  unsigned i = 0;
  TNode t;
  for (; i < conjunctions.size(); ++i) {
    t = conjunctions[i];

    // Expand explanation resulting from propagating a ROW lemma
    if (t.getKind() == kind::OR) {
      if ((explained.find(t) == explained.end())) {
        Assert(t[1].getKind() == kind::EQUAL);
        d_equalityEngine.explainEquality(t[1][0], t[1][1], false, conjunctions);
        explained.insert(t);
      }
      continue;
    }
    all.insert(t);
  }

  Assert(all.size() > 0);
  if (all.size() == 1) {
    // All the same, or just one
    return *(all.begin());
  }

  NodeBuilder<> conjunction(kind::AND);
  std::set<TNode>::const_iterator it = all.begin();
  std::set<TNode>::const_iterator it_end = all.end();
  while (it != it_end) {
    conjunction << *it;
    ++ it;
  }

  return conjunction;
}


void TheoryArrays::setNonLinear(TNode a)
{
  if (d_infoMap.isNonLinear(a)) return;

  Trace("arrays") << spaces(getSatContext()->getLevel()) << "Arrays::setNonLinear (" << a << ")\n";
  d_infoMap.setNonLinear(a);
  ++d_numNonLinear;

  const CTNodeList* i_a = d_infoMap.getIndices(a);
  const CTNodeList* st_a = d_infoMap.getStores(a);
  const CTNodeList* inst_a = d_infoMap.getInStores(a);

  CTNodeList::const_iterator it = st_a->begin();

  // Propagate non-linearity down chain of stores
  for(; it!= st_a->end(); ++it) {
    TNode store = *it;
    Assert(store.getKind()==kind::STORE);
    setNonLinear(store[0]);
  }

  // Instantiate ROW lemmas that were ignored before
  CTNodeList::const_iterator it2 = i_a->begin();
  RowLemmaType lem;
  for(; it2 != i_a->end(); ++it2 ) {
    TNode i = *it2;
    it = inst_a->begin();
    for ( ; it !=inst_a->end(); ++it) {
      TNode store = *it;
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
      if (d_equalityEngine.areEqual(e1, b)) {
        apply = true;
      }
    }
  }

  if (apply) {
    NodeManager* nm = NodeManager::currentNM();
    d_infoMap.setRIntro1Applied(s);
    Node ni = nm->mkNode(kind::SELECT, s, s[1]);
    preRegisterTerm(ni);
    d_equalityEngine.assertEquality(ni.eqNode(s[2]), true, d_true);
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
    Trace("arrays-merge") << spaces(getSatContext()->getLevel()) << "Arrays::merge: " << a << "," << b << ")\n";

    checkRIntro1(a, b);
    checkRIntro1(b, a);

    if (d_useNonLinearOpt) {
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
  Trace("arrays-cri")<<"Arrays::checkStore "<<a<<"\n";

  if(Trace.isOn("arrays-cri")) {
    d_infoMap.getInfo(a)->print();
  }
  Assert(a.getType().isArray());
  Assert(a.getKind()==kind::STORE);
  TNode b = a[0];
  TNode i = a[1];

  TNode brep = d_equalityEngine.getRepresentative(b);

  if (!d_useNonLinearOpt || d_infoMap.isNonLinear(brep)) {
    const CTNodeList* js = d_infoMap.getIndices(brep);
    CTNodeList::const_iterator it = js->begin();

    RowLemmaType lem;
    for(; it!= js->end(); ++it) {
      TNode j = *it;
      if (i == j) continue;
      lem = make_quad(a,b,i,j);
      Trace("arrays-lem") << spaces(getSatContext()->getLevel()) <<"Arrays::checkStore ("<<a<<", "<<b<<", "<<i<<", "<<j<<")\n";
      queueRowLemma(lem);
    }
  }
}


void TheoryArrays::checkRowForIndex(TNode i, TNode a)
{
  Trace("arrays-cri")<<"Arrays::checkRowForIndex "<<a<<"\n";
  Trace("arrays-cri")<<"                   index "<<i<<"\n";

  if(Trace.isOn("arrays-cri")) {
    d_infoMap.getInfo(a)->print();
  }
  Assert(a.getType().isArray());
  Assert(d_equalityEngine.getRepresentative(a) == a);

  const CTNodeList* stores = d_infoMap.getStores(a);
  const CTNodeList* instores = d_infoMap.getInStores(a);
  CTNodeList::const_iterator it = stores->begin();
  RowLemmaType lem;

  for(; it!= stores->end(); ++it) {
    TNode store = *it;
    Assert(store.getKind()==kind::STORE);
    TNode j = store[1];
    if (i == j) continue;
    lem = make_quad(store, store[0], j, i);
    Trace("arrays-lem") << spaces(getSatContext()->getLevel()) <<"Arrays::checkRowForIndex ("<<store<<", "<<store[0]<<", "<<j<<", "<<i<<")\n";
    queueRowLemma(lem);
  }

  if (!d_useNonLinearOpt || d_infoMap.isNonLinear(a)) {
    it = instores->begin();
    for(; it!= instores->end(); ++it) {
      TNode instore = *it;
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
  Trace("arrays-crl")<<"Arrays::checkLemmas begin \n"<<a<<"\n";
  if(Trace.isOn("arrays-crl"))
    d_infoMap.getInfo(a)->print();
  Trace("arrays-crl")<<"  ------------  and "<<b<<"\n";
  if(Trace.isOn("arrays-crl"))
    d_infoMap.getInfo(b)->print();

  const CTNodeList* i_a = d_infoMap.getIndices(a);
  const CTNodeList* st_b = d_infoMap.getStores(b);
  const CTNodeList* inst_b = d_infoMap.getInStores(b);

  CTNodeList::const_iterator it = i_a->begin();
  CTNodeList::const_iterator its;

  RowLemmaType lem;

  for( ; it != i_a->end(); ++it ) {
    TNode i = *it;
    its = st_b->begin();
    for ( ; its != st_b->end(); ++its) {
      TNode store = *its;
      Assert(store.getKind() == kind::STORE);
      TNode j = store[1];
      TNode c = store[0];
      lem = make_quad(store, c, j, i);
      Trace("arrays-lem") << spaces(getSatContext()->getLevel()) <<"Arrays::checkRowLemmas ("<<store<<", "<<c<<", "<<j<<", "<<i<<")\n";
      queueRowLemma(lem);
    }
  }

  if (!d_useNonLinearOpt || d_infoMap.isNonLinear(b)) {
    for(it = i_a->begin() ; it != i_a->end(); ++it ) {
      TNode i = *it;
      its = inst_b->begin();
      for ( ; its !=inst_b->end(); ++its) {
        TNode store = *its;
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
  if (d_conflict || d_RowAlreadyAdded.count(lem) != 0) {
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
    if (d_equalityEngine.areDisequal(i,j)) {
      Trace("arrays-lem") << spaces(getSatContext()->getLevel()) <<"Arrays::queueRowLemma: propagating aj = bj ("<<aj<<", "<<bj<<")\n";
      Node aj_eq_bj = aj.eqNode(bj);
      Node i_eq_j = i.eqNode(j);
      Node reason = nm->mkNode(kind::OR, aj_eq_bj, i_eq_j);
      d_permRef.push_back(reason);
      if (!ajExists) {
        preRegisterTerm(aj);
      }
      if (!bjExists) {
        preRegisterTerm(bj);
      }
      d_equalityEngine.assertEquality(aj_eq_bj, true, reason);
      ++d_numProp;
      return;
    }
    if (bothExist && d_equalityEngine.areDisequal(aj,bj)) {
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
  if (d_eagerIndexSplitting && !bothExist && !d_equalityEngine.areDisequal(i,j)) {
    Node split = d_valuation.ensureLiteral(i.eqNode(j));
    d_out->propagateAsDecision(split);
  }

  // TODO: maybe add triggers here

  if (d_eagerLemmas || bothExist) {

    // Make sure that any terms introduced by rewriting are appropriately stored in the equality database
    Node aj2 = Rewriter::rewrite(aj);
    if (aj != aj2) {
      if (!ajExists) {
        preRegisterTerm(aj);
      }
      if (!d_equalityEngine.hasTerm(aj2)) {
        preRegisterTerm(aj2);
      }
      d_equalityEngine.assertEquality(aj.eqNode(aj2), true, d_true);
    }
    Node bj2 = Rewriter::rewrite(bj);
    if (bj != bj2) {
      if (!bjExists) {
        preRegisterTerm(bj);
      }
      if (!d_equalityEngine.hasTerm(bj2)) {
        preRegisterTerm(bj2);
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
        preRegisterTerm(aj2);
      }
      if (!d_equalityEngine.hasTerm(bj2)) {
        preRegisterTerm(bj2);
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


void TheoryArrays::dischargeLemmas()
{
  size_t sz = d_RowQueue.size();
  for (unsigned count = 0; count < sz; ++count) {
    RowLemmaType l = d_RowQueue.front();
    d_RowQueue.pop();
    if (d_RowAlreadyAdded.count(l) != 0) {
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
    if (d_equalityEngine.areEqual(i,j) ||
        d_equalityEngine.areEqual(a,b) ||
        (ajExists && bjExists && d_equalityEngine.areEqual(aj,bj))) {
      d_RowQueue.push(l);
      continue;
    }

    // Make sure that any terms introduced by rewriting are appropriately stored in the equality database
    Node aj2 = Rewriter::rewrite(aj);
    if (aj != aj2) {
      if (!ajExists) {
        preRegisterTerm(aj);
      }
      if (!d_equalityEngine.hasTerm(aj2)) {
        preRegisterTerm(aj2);
      }
      d_equalityEngine.assertEquality(aj.eqNode(aj2), true, d_true);
    }
    Node bj2 = Rewriter::rewrite(bj);
    if (bj != bj2) {
      if (!bjExists) {
        preRegisterTerm(bj);
      }
      if (!d_equalityEngine.hasTerm(bj2)) {
        preRegisterTerm(bj2);
      }
      d_equalityEngine.assertEquality(bj.eqNode(bj2), true, d_true);
    }
    if (aj2 == bj2) {
      d_RowQueue.push(l);
      continue;
    }

    // construct lemma
    Node eq1 = aj2.eqNode(bj2);
    Node eq1_r = Rewriter::rewrite(eq1);
    if (eq1_r == d_true) {
      if (!d_equalityEngine.hasTerm(aj2)) {
        preRegisterTerm(aj2);
      }
      if (!d_equalityEngine.hasTerm(bj2)) {
        preRegisterTerm(bj2);
      }
      d_equalityEngine.assertEquality(eq1, true, d_true);
      d_RowQueue.push(l);
      continue;
    }

    Node eq2 = i.eqNode(j);
    Node eq2_r = Rewriter::rewrite(eq2);
    if (eq2_r == d_true) {
      d_equalityEngine.assertEquality(eq2, true, d_true);
      d_RowQueue.push(l);
      continue;
    }
    
    Node lem = nm->mkNode(kind::OR, eq2_r, eq1_r);

    Trace("arrays-lem")<<"Arrays::addRowLemma adding "<<lem<<"\n";
    d_RowAlreadyAdded.insert(l);
    d_out->lemma(lem);
    ++d_numRow;
  }
}


}/* CVC4::theory::arrays namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */
