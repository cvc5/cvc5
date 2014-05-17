/*********************                                                        */
/*! \file theory_uf.cpp
 ** \verbatim
 ** Original author: Tim King
 ** Major contributors: Morgan Deters, Dejan Jovanovic
 ** Minor contributors (to current version): Clark Barrett, Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2013  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief This is the interface to TheoryUF implementations
 **
 ** This is the interface to TheoryUF implementations.  All
 ** implementations of TheoryUF should inherit from this class.
 **/

#include "theory/uf/theory_uf.h"
#include "theory/uf/options.h"
#include "theory/quantifiers/options.h"
#include "theory/uf/theory_uf_strong_solver.h"
#include "theory/theory_model.h"
#include "theory/type_enumerator.h"

using namespace std;
using namespace CVC4;
using namespace CVC4::theory;
using namespace CVC4::theory::uf;

/** Constructs a new instance of TheoryUF w.r.t. the provided context.*/
TheoryUF::TheoryUF(context::Context* c, context::UserContext* u, OutputChannel& out, Valuation valuation, const LogicInfo& logicInfo) :
  Theory(THEORY_UF, c, u, out, valuation, logicInfo),
  d_notify(*this),
  /* The strong theory solver can be notified by EqualityEngine::init(),
   * so make sure it's initialized first. */
  d_thss(NULL),
  d_equalityEngine(d_notify, c, "theory::uf::TheoryUF"),
  d_conflict(c, false),
  d_literalsToPropagate(c),
  d_literalsToPropagateIndex(c, 0),
  d_functionsTerms(c),
  d_symb(u)
{
  // The kinds we are treating as function application in congruence
  d_equalityEngine.addFunctionKind(kind::APPLY_UF);
}

TheoryUF::~TheoryUF() {
  // destruct all ppRewrite() callbacks
  for(RegisterPpRewrites::iterator i = d_registeredPpRewrites.begin();
      i != d_registeredPpRewrites.end();
      ++i) {
    delete i->second;
  }
  delete d_thss;
}

void TheoryUF::setMasterEqualityEngine(eq::EqualityEngine* eq) {
  d_equalityEngine.setMasterEqualityEngine(eq);
}

void TheoryUF::finishInit() {
  // initialize the strong solver
  if (options::finiteModelFind()) {
    d_thss = new StrongSolverTheoryUF(getSatContext(), getUserContext(), *d_out, this);
  }
}

static Node mkAnd(const std::vector<TNode>& conjunctions) {
  Assert(conjunctions.size() > 0);

  std::set<TNode> all;
  all.insert(conjunctions.begin(), conjunctions.end());

  if (all.size() == 1) {
    // All the same, or just one
    return conjunctions[0];
  }

  NodeBuilder<> conjunction(kind::AND);
  std::set<TNode>::const_iterator it = all.begin();
  std::set<TNode>::const_iterator it_end = all.end();
  while (it != it_end) {
    conjunction << *it;
    ++ it;
  }

  return conjunction;
}/* mkAnd() */

void TheoryUF::check(Effort level) {
  while (!done() && !d_conflict)
  {
    // Get all the assertions
    Assertion assertion = get();
    TNode fact = assertion.assertion;

    Debug("uf") << "TheoryUF::check(): processing " << fact << std::endl;
    if (d_thss != NULL) {
      bool isDecision = d_valuation.isSatLiteral(fact) && d_valuation.isDecision(fact);
      d_thss->assertNode(fact, isDecision);
      if( d_thss->isConflict() ){
        d_conflict = true;
        return;
      }
    }

    // Do the work
    bool polarity = fact.getKind() != kind::NOT;
    TNode atom = polarity ? fact : fact[0];
    if (atom.getKind() == kind::EQUAL) {
      d_equalityEngine.assertEquality(atom, polarity, fact);
    } else if (atom.getKind() == kind::CARDINALITY_CONSTRAINT || atom.getKind() == kind::COMBINED_CARDINALITY_CONSTRAINT) {
      if( d_thss == NULL ){
        std::stringstream ss;
        ss << "Cardinality constraint " << atom << " was asserted, but the logic does not allow it." << std::endl;
        ss << "Try using a logic containing \"UFC\"." << std::endl;
        throw Exception( ss.str() );
      }
    } else {
      d_equalityEngine.assertPredicate(atom, polarity, fact);
    }
  }


  if (d_thss != NULL && ! d_conflict) {
    d_thss->check(level);
    if( d_thss->isConflict() ){
      d_conflict = true;
    }
  }

}/* TheoryUF::check() */

void TheoryUF::preRegisterTerm(TNode node) {
  Debug("uf") << "TheoryUF::preRegisterTerm(" << node << ")" << std::endl;

  if (d_thss != NULL) {
    d_thss->preRegisterTerm(node);
  }

  switch (node.getKind()) {
  case kind::EQUAL:
    // Add the trigger for equality
    d_equalityEngine.addTriggerEquality(node);
    break;
  case kind::APPLY_UF:
    // Maybe it's a predicate
    if (node.getType().isBoolean()) {
      // Get triggered for both equal and dis-equal
      d_equalityEngine.addTriggerPredicate(node);
    } else {
      // Function applications/predicates
      d_equalityEngine.addTerm(node);
    }
    // Remember the function and predicate terms
    d_functionsTerms.push_back(node);
    break;
  case kind::CARDINALITY_CONSTRAINT:
  case kind::COMBINED_CARDINALITY_CONSTRAINT:
    //do nothing
    break;
  default:
    // Variables etc
    d_equalityEngine.addTerm(node);
    break;
  }
}/* TheoryUF::preRegisterTerm() */

bool TheoryUF::propagate(TNode literal) {
  Debug("uf::propagate") << "TheoryUF::propagate(" << literal  << ")" << std::endl;
  // If already in conflict, no more propagation
  if (d_conflict) {
    Debug("uf::propagate") << "TheoryUF::propagate(" << literal << "): already in conflict" << std::endl;
    return false;
  }
  // Propagate out
  bool ok = d_out->propagate(literal);
  if (!ok) {
    d_conflict = true;
  }
  return ok;
}/* TheoryUF::propagate(TNode) */

void TheoryUF::propagate(Effort effort) {
  //if (d_thss != NULL) {
  //  return d_thss->propagate(effort);
  //}
}

Node TheoryUF::getNextDecisionRequest(){
  if (d_thss != NULL && !d_conflict) {
    return d_thss->getNextDecisionRequest();
  }else{
    return Node::null();
  }
}

void TheoryUF::explain(TNode literal, std::vector<TNode>& assumptions) {
  // Do the work
  bool polarity = literal.getKind() != kind::NOT;
  TNode atom = polarity ? literal : literal[0];
  eq::EqProof * eqp = d_proofEnabled ? new eq::EqProof : NULL;
  if (atom.getKind() == kind::EQUAL || atom.getKind() == kind::IFF) {
    d_equalityEngine.explainEquality(atom[0], atom[1], polarity, assumptions, eqp);
  } else {
    d_equalityEngine.explainPredicate(atom, polarity, assumptions, eqp);
  }
  //for now, just print debug
  //TODO : send the proof outwards : d_out->conflict( lem, eqp );
  if( eqp ){
    eqp->debug_print("uf-pf");
  }
}

Node TheoryUF::explain(TNode literal) {
  Debug("uf") << "TheoryUF::explain(" << literal << ")" << std::endl;
  std::vector<TNode> assumptions;
  explain(literal, assumptions);
  return mkAnd(assumptions);
}

void TheoryUF::collectModelInfo( TheoryModel* m, bool fullModel ){
  m->assertEqualityEngine( &d_equalityEngine );
  // if( fullModel ){
  //   std::map< TypeNode, TypeEnumerator* > type_enums;
  //   //must choose proper representatives
  //   // for each equivalence class, specify fresh constant as representative
  //   eq::EqClassesIterator eqcs_i = eq::EqClassesIterator( &d_equalityEngine );
  //   while( !eqcs_i.isFinished() ){
  //     Node eqc = (*eqcs_i);
  //     TypeNode tn = eqc.getType();
  //     if( tn.isSort() ){
  //       if( type_enums.find( tn )==type_enums.end() ){
  //         type_enums[tn] = new TypeEnumerator( tn );
  //       }
  //       Node rep = *(*type_enums[tn]);
  //       ++(*type_enums[tn]);
  //       //specify the constant as the representative
  //       m->assertEquality( eqc, rep, true );
  //       m->assertRepresentative( rep );
  //     }
  //     ++eqcs_i;
  //   }
  // }
}

void TheoryUF::presolve() {
  // TimerStat::CodeTimer codeTimer(d_presolveTimer);

  Debug("uf") << "uf: begin presolve()" << endl;
  if(options::ufSymmetryBreaker()) {
    vector<Node> newClauses;
    d_symb.apply(newClauses);
    for(vector<Node>::const_iterator i = newClauses.begin();
        i != newClauses.end();
        ++i) {
      d_out->lemma(*i);
    }
  }
  Debug("uf") << "uf: end presolve()" << endl;
}

void TheoryUF::ppStaticLearn(TNode n, NodeBuilder<>& learned) {
  //TimerStat::CodeTimer codeTimer(d_staticLearningTimer);

  vector<TNode> workList;
  workList.push_back(n);
  __gnu_cxx::hash_set<TNode, TNodeHashFunction> processed;

  while(!workList.empty()) {
    n = workList.back();

    if(n.getKind() == kind::FORALL || n.getKind() == kind::EXISTS) {
      // unsafe to go under quantifiers; we might pull bound vars out of scope!
      processed.insert(n);
      workList.pop_back();
      continue;
    }

    bool unprocessedChildren = false;
    for(TNode::iterator i = n.begin(), iend = n.end(); i != iend; ++i) {
      if(processed.find(*i) == processed.end()) {
        // unprocessed child
        workList.push_back(*i);
        unprocessedChildren = true;
      }
    }

    if(unprocessedChildren) {
      continue;
    }

    workList.pop_back();
    // has node n been processed in the meantime ?
    if(processed.find(n) != processed.end()) {
      continue;
    }
    processed.insert(n);

    // == DIAMONDS ==

    Debug("diamonds") << "===================== looking at" << endl
                      << n << endl;

    // binary OR of binary ANDs of EQUALities
    if(n.getKind() == kind::OR && n.getNumChildren() == 2 &&
       n[0].getKind() == kind::AND && n[0].getNumChildren() == 2 &&
       n[1].getKind() == kind::AND && n[1].getNumChildren() == 2 &&
       (n[0][0].getKind() == kind::EQUAL || n[0][0].getKind() == kind::IFF) &&
       (n[0][1].getKind() == kind::EQUAL || n[0][1].getKind() == kind::IFF) &&
       (n[1][0].getKind() == kind::EQUAL || n[1][0].getKind() == kind::IFF) &&
       (n[1][1].getKind() == kind::EQUAL || n[1][1].getKind() == kind::IFF)) {
      // now we have (a = b && c = d) || (e = f && g = h)

      Debug("diamonds") << "has form of a diamond!" << endl;

      TNode
        a = n[0][0][0], b = n[0][0][1],
        c = n[0][1][0], d = n[0][1][1],
        e = n[1][0][0], f = n[1][0][1],
        g = n[1][1][0], h = n[1][1][1];

      // test that one of {a, b} = one of {c, d}, and make "b" the
      // shared node (i.e. put in the form (a = b && b = d))
      // note we don't actually care about the shared ones, so the
      // "swaps" below are one-sided, ignoring b and c
      if(a == c) {
        a = b;
      } else if(a == d) {
        a = b;
        d = c;
      } else if(b == c) {
        // nothing to do
      } else if(b == d) {
        d = c;
      } else {
        // condition not satisfied
        Debug("diamonds") << "+ A fails" << endl;
        continue;
      }

      Debug("diamonds") << "+ A holds" << endl;

      // same: one of {e, f} = one of {g, h}, and make "f" the
      // shared node (i.e. put in the form (e = f && f = h))
      if(e == g) {
        e = f;
      } else if(e == h) {
        e = f;
        h = g;
      } else if(f == g) {
        // nothing to do
      } else if(f == h) {
        h = g;
      } else {
        // condition not satisfied
        Debug("diamonds") << "+ B fails" << endl;
        continue;
      }

      Debug("diamonds") << "+ B holds" << endl;

      // now we have (a = b && b = d) || (e = f && f = h)
      // test that {a, d} == {e, h}
      if( (a == e && d == h) ||
          (a == h && d == e) ) {
        // learn: n implies a == d
        Debug("diamonds") << "+ C holds" << endl;
        Node newEquality = a.getType().isBoolean() ? a.iffNode(d) : a.eqNode(d);
        Debug("diamonds") << "  ==> " << newEquality << endl;
        learned << n.impNode(newEquality);
      } else {
        Debug("diamonds") << "+ C fails" << endl;
      }
    }
  }

  if(options::ufSymmetryBreaker()) {
    d_symb.assertFormula(n);
  }
}/* TheoryUF::ppStaticLearn() */

EqualityStatus TheoryUF::getEqualityStatus(TNode a, TNode b) {

  // Check for equality (simplest)
  if (d_equalityEngine.areEqual(a, b)) {
    // The terms are implied to be equal
    return EQUALITY_TRUE;
  }

  // Check for disequality
  if (d_equalityEngine.areDisequal(a, b, false)) {
    // The terms are implied to be dis-equal
    return EQUALITY_FALSE;
  }

  // All other terms we interpret as dis-equal in the model
  return EQUALITY_FALSE_IN_MODEL;
}

void TheoryUF::addSharedTerm(TNode t) {
  Debug("uf::sharing") << "TheoryUF::addSharedTerm(" << t << ")" << std::endl;
  d_equalityEngine.addTriggerTerm(t, THEORY_UF);
}

void TheoryUF::computeCareGraph() {

  if (d_sharedTerms.size() > 0) {

    vector< pair<TNode, TNode> > currentPairs;

    // Go through the function terms and see if there are any to split on
    unsigned functionTerms = d_functionsTerms.size();
    for (unsigned i = 0; i < functionTerms; ++ i) {

      TNode f1 = d_functionsTerms[i];
      Node op = f1.getOperator();

      for (unsigned j = i + 1; j < functionTerms; ++ j) {

        TNode f2 = d_functionsTerms[j];

        // If the operators are not the same, we can skip this pair
        if (f2.getOperator() != op) {
          continue;
        }

        Debug("uf::sharing") << "TheoryUf::computeCareGraph(): checking function " << f1 << " and " << f2 << std::endl;

        // If the terms are already known to be equal, we are also in good shape
        if (d_equalityEngine.areEqual(f1, f2)) {
          Debug("uf::sharing") << "TheoryUf::computeCareGraph(): equal, skipping" << std::endl;
          continue;
        }

        // We have two functions f(x1, ..., xn) and f(y1, ..., yn) no known to be equal
        // We split on the argument pairs that are are not known, unless there is some
        // argument pair that is already dis-equal.
        bool somePairIsDisequal = false;
        currentPairs.clear();
        for (unsigned k = 0; k < f1.getNumChildren(); ++ k) {

          TNode x = f1[k];
          TNode y = f2[k];

          Debug("uf::sharing") << "TheoryUf::computeCareGraph(): checking arguments " << x << " and " << y << std::endl;

          if (d_equalityEngine.areDisequal(x, y, false)) {
            // Mark that there is a dis-equal pair and break
            somePairIsDisequal = true;
            Debug("uf::sharing") << "TheoryUf::computeCareGraph(): disequal, disregarding all" << std::endl;
            break;
          }

          if (d_equalityEngine.areEqual(x, y)) {
            // We don't need this one
            Debug("uf::sharing") << "TheoryUf::computeCareGraph(): equal" << std::endl;
            continue;
          }

          if (!d_equalityEngine.isTriggerTerm(x, THEORY_UF) || !d_equalityEngine.isTriggerTerm(y, THEORY_UF)) {
            // Not connected to shared terms, we don't care
            continue;
          }

          // Get representative trigger terms
          TNode x_shared = d_equalityEngine.getTriggerTermRepresentative(x, THEORY_UF);
          TNode y_shared = d_equalityEngine.getTriggerTermRepresentative(y, THEORY_UF);

          EqualityStatus eqStatusDomain = d_valuation.getEqualityStatus(x_shared, y_shared);
          switch (eqStatusDomain) {
          case EQUALITY_FALSE_AND_PROPAGATED:
          case EQUALITY_FALSE:
          case EQUALITY_FALSE_IN_MODEL:
            somePairIsDisequal = true;
            continue;
            break;
          default:
            break;
            // nothing
          }

          // Otherwise, we need to figure it out
          Debug("uf::sharing") << "TheoryUf::computeCareGraph(): adding to care-graph" << std::endl;
          currentPairs.push_back(make_pair(x_shared, y_shared));
        }

        if (!somePairIsDisequal) {
          for (unsigned i = 0; i < currentPairs.size(); ++ i) {
            addCarePair(currentPairs[i].first, currentPairs[i].second);
          }
        }
      }
    }
  }
}/* TheoryUF::computeCareGraph() */

void TheoryUF::conflict(TNode a, TNode b) {
  //TODO: create EqProof at this level if d_proofEnabled = true
  if (a.getKind() == kind::CONST_BOOLEAN) {
    d_conflictNode = explain(a.iffNode(b));
  } else {
    d_conflictNode = explain(a.eqNode(b));
  }
  d_out->conflict(d_conflictNode);
  d_conflict = true;
}

void TheoryUF::eqNotifyNewClass(TNode t) {
  if (d_thss != NULL) {
    d_thss->newEqClass(t);
  }
}

void TheoryUF::eqNotifyPreMerge(TNode t1, TNode t2) {
  if (getLogicInfo().isQuantified()) {
    //getQuantifiersEngine()->getEfficientEMatcher()->merge( t1, t2 );
  }
}

void TheoryUF::eqNotifyPostMerge(TNode t1, TNode t2) {
  if (d_thss != NULL) {
    d_thss->merge(t1, t2);
  }
}

void TheoryUF::eqNotifyDisequal(TNode t1, TNode t2, TNode reason) {
  if (d_thss != NULL) {
    d_thss->assertDisequal(t1, t2, reason);
  }
}

Node TheoryUF::ppRewrite(TNode node) {

  if (node.getKind() != kind::APPLY_UF) {
    return node;
  }

  // perform the callbacks requested by TheoryUF::registerPpRewrite()
  RegisterPpRewrites::iterator c = d_registeredPpRewrites.find(node.getOperator());
  if (c == d_registeredPpRewrites.end()) {
    return node;
  } else {
    Node res = c->second->ppRewrite(node);
    if (res != node) {
      return ppRewrite(res);
    } else {
      return res;
    }
  }
}

