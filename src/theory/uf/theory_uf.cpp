/*********************                                                        */
/*! \file theory_uf.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Morgan Deters, Andrew Reynolds, Dejan Jovanovic
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2017 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief This is the interface to TheoryUF implementations
 **
 ** This is the interface to TheoryUF implementations.  All
 ** implementations of TheoryUF should inherit from this class.
 **/

#include "theory/uf/theory_uf.h"

#include <memory>

#include "options/quantifiers_options.h"
#include "options/smt_options.h"
#include "options/uf_options.h"
#include "proof/proof_manager.h"
#include "proof/theory_proof.h"
#include "proof/uf_proof.h"
#include "theory/theory_model.h"
#include "theory/type_enumerator.h"
#include "theory/uf/theory_uf_strong_solver.h"
#include "theory/quantifiers/term_database.h"
#include "options/theory_options.h"
#include "theory/uf/theory_uf_rewriter.h"

using namespace std;

namespace CVC4 {
namespace theory {
namespace uf {

/** Constructs a new instance of TheoryUF w.r.t. the provided context.*/
TheoryUF::TheoryUF(context::Context* c, context::UserContext* u,
                   OutputChannel& out, Valuation valuation,
                   const LogicInfo& logicInfo, std::string instanceName)
    : Theory(THEORY_UF, c, u, out, valuation, logicInfo, instanceName),
      d_notify(*this),
      /* The strong theory solver can be notified by EqualityEngine::init(),
       * so make sure it's initialized first. */
      d_thss(NULL),
      d_equalityEngine(d_notify, c, instanceName + "theory::uf::ee", true),
      d_conflict(c, false),
      d_extensionality_deq(u),
      d_uf_std_skolem(u),
      d_functionsTerms(c),
      d_symb(u, instanceName)
{
  d_true = NodeManager::currentNM()->mkConst( true );

  // The kinds we are treating as function application in congruence
  d_equalityEngine.addFunctionKind(kind::APPLY_UF, false, options::ufHo());
  if( options::ufHo() ){
    d_equalityEngine.addFunctionKind(kind::HO_APPLY);
  }
}

TheoryUF::~TheoryUF() {
  delete d_thss;
}

void TheoryUF::setMasterEqualityEngine(eq::EqualityEngine* eq) {
  d_equalityEngine.setMasterEqualityEngine(eq);
}

void TheoryUF::finishInit() {
  // initialize the strong solver
  if (options::finiteModelFind() && options::ufssMode()!=UF_SS_NONE) {
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
  if (done() && !fullEffort(level)) {
    return;
  }
  getOutputChannel().spendResource(options::theoryCheckStep());
  TimerStat::CodeTimer checkTimer(d_checkTime);

  while (!done() && !d_conflict)
  {
    // Get all the assertions
    Assertion assertion = get();
    TNode fact = assertion.assertion;

    Debug("uf") << "TheoryUF::check(): processing " << fact << std::endl;
    Debug("uf") << "Term's theory: " << theory::Theory::theoryOf(fact.toExpr()) << std::endl;

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
      if( options::ufHo() && options::ufHoExt() ){
        if( !polarity && !d_conflict && atom[0].getType().isFunction() ){
          applyExtensionality( fact );
        }
      }
    } else if (atom.getKind() == kind::CARDINALITY_CONSTRAINT || atom.getKind() == kind::COMBINED_CARDINALITY_CONSTRAINT) {
      if( d_thss == NULL ){
        if( !getLogicInfo().hasCardinalityConstraints() ){
          std::stringstream ss;
          ss << "Cardinality constraint " << atom << " was asserted, but the logic does not allow it." << std::endl;
          ss << "Try using a logic containing \"UFC\"." << std::endl;
          throw Exception( ss.str() );
        }else{
          // support for cardinality constraints is not enabled, set incomplete
          d_out->setIncomplete();
        } 
      }
      //needed for models
      if( options::produceModels() ){
        d_equalityEngine.assertPredicate(atom, polarity, fact);
      }
    } else {
      d_equalityEngine.assertPredicate(atom, polarity, fact);
    }
  }

  if(! d_conflict ){
    if (d_thss != NULL) {
      d_thss->check(level);
      if( d_thss->isConflict() ){
        d_conflict = true;
      }
    }
    if(! d_conflict && fullEffort(level) ){
      if( options::ufHo() ){
        checkHigherOrder();
      }
    }
  }
}/* TheoryUF::check() */

Node TheoryUF::getApplyUfForHoApply( Node node ) {
  Assert( node[0].getType().getNumChildren()==2 );
  std::vector< TNode > args;
  Node f = TheoryUfRewriter::decomposeHoApply( node, args, true );
  Node new_f = f;
  if( !TheoryUfRewriter::canUseAsApplyUfOperator( f ) ){
    NodeNodeMap::const_iterator itus = d_uf_std_skolem.find( f );
    if( itus==d_uf_std_skolem.end() ){
      // introduce skolem to make a standard APPLY_UF
      new_f = NodeManager::currentNM()->mkSkolem( "app_uf", f.getType() );
      Node lem = new_f.eqNode( f );
      Trace("uf-ho-lemma") << "uf-ho-lemma : Skolem definition for apply-conversion : " << lem << std::endl;
      d_out->lemma( lem );
      d_uf_std_skolem[f] = new_f;
    }else{
      new_f = (*itus).second;
    }
  }
  Assert( TheoryUfRewriter::canUseAsApplyUfOperator( new_f ) );
  args[0] = new_f;
  Node ret = NodeManager::currentNM()->mkNode( kind::APPLY_UF, args );
  return ret;
}

Node TheoryUF::getOperatorForApplyTerm( TNode node ) {
  Assert( node.getKind()==kind::APPLY_UF || node.getKind()==kind::HO_APPLY );
  if( node.getKind()==kind::APPLY_UF ){
    return node.getOperator();
  }else{
    return d_equalityEngine.getRepresentative( node[0] );
  }
}

unsigned TheoryUF::getArgumentStartIndexForApplyTerm( TNode node ) {
  Assert( node.getKind()==kind::APPLY_UF || node.getKind()==kind::HO_APPLY );
  return node.getKind()==kind::APPLY_UF ? 0 : 1;
}

Node TheoryUF::expandDefinition(LogicRequest &logicRequest, Node node) {
  Trace("uf-ho-debug") << "uf-ho-debug : expanding definition : " << node << std::endl;
  if( node.getKind()==kind::HO_APPLY ){
    if( !options::ufHo() ){
      std::stringstream ss;
      ss << "Partial function applications are not supported in default mode, try --uf-ho.";
      throw LogicException(ss.str());
    }
    // convert HO_APPLY to APPLY_UF if fully applied
    if( node[0].getType().getNumChildren()==2 ){
      Trace("uf-ho") << "uf-ho : expanding definition : " << node << std::endl;
      Node ret = getApplyUfForHoApply( node );
      Trace("uf-ho") << "uf-ho : expandDefinition : " << node << " to " << ret << std::endl;
      return ret;
    }
  }
  return node;
}

void TheoryUF::preRegisterTerm(TNode node) {
  Debug("uf") << "TheoryUF::preRegisterTerm(" << node << ")" << std::endl;

  if (d_thss != NULL) {
    d_thss->preRegisterTerm(node);
  }

  // we always use APPLY_UF if not higher-order, HO_APPLY if higher-order
  //Assert( node.getKind()!=kind::APPLY_UF || !options::ufHo() );
  Assert( node.getKind()!=kind::HO_APPLY || options::ufHo() );

  switch (node.getKind()) {
  case kind::EQUAL:
    // Add the trigger for equality
    d_equalityEngine.addTriggerEquality(node);
    break;
  case kind::APPLY_UF:
  case kind::HO_APPLY:
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

Node TheoryUF::getNextDecisionRequest( unsigned& priority ){
  if (d_thss != NULL && !d_conflict) {
    return d_thss->getNextDecisionRequest( priority );
  }else{
    return Node::null();
  }
}

void TheoryUF::explain(TNode literal, std::vector<TNode>& assumptions, eq::EqProof* pf) {
  // Do the work
  bool polarity = literal.getKind() != kind::NOT;
  TNode atom = polarity ? literal : literal[0];
  if (atom.getKind() == kind::EQUAL) {
    d_equalityEngine.explainEquality(atom[0], atom[1], polarity, assumptions, pf);
  } else {
    d_equalityEngine.explainPredicate(atom, polarity, assumptions, pf);
  }
  if( pf ){
    Debug("pf::uf") << std::endl;
    pf->debug_print("pf::uf");
  }

  Debug("pf::uf") << "UF: explain( " << literal << " ):" << std::endl << "\t";
  for (unsigned i = 0; i < assumptions.size(); ++i) {
    Debug("pf::uf") << assumptions[i] << " ";
  }
  Debug("pf::uf") << std::endl;
}

Node TheoryUF::explain(TNode literal) {
  return explain(literal, NULL);
}

Node TheoryUF::explain(TNode literal, eq::EqProof* pf) {
  Debug("uf") << "TheoryUF::explain(" << literal << ")" << std::endl;
  std::vector<TNode> assumptions;
  explain(literal, assumptions, pf);
  return mkAnd(assumptions);
}

bool TheoryUF::collectModelInfo(TheoryModel* m)
{
  Debug("uf") << "UF : collectModelInfo " << std::endl;
  set<Node> termSet;

  // Compute terms appearing in assertions and shared terms
  computeRelevantTerms(termSet);

  if (!m->assertEqualityEngine(&d_equalityEngine, &termSet))
  {
    return false;
  }

  if( options::ufHo() ){
    for( std::set<Node>::iterator it = termSet.begin(); it != termSet.end(); ++it ){
      Node n = *it;
      if( n.getKind()==kind::APPLY_UF ){
        // for model-building with ufHo, we require that APPLY_UF is always expanded to HO_APPLY
        Node hn = TheoryUfRewriter::getHoApplyForApplyUf( n );
        if (!m->assertEquality(n, hn, true))
        {
          return false;
        }
      }
    }
  }

  Debug("uf") << "UF : finish collectModelInfo " << std::endl;
  return true;
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
      Debug("uf") << "uf: generating a lemma: " << *i << std::endl;
      d_out->lemma(*i);
    }
  }
  if( d_thss ){
    d_thss->presolve();
  }
  Debug("uf") << "uf: end presolve()" << endl;
}

void TheoryUF::ppStaticLearn(TNode n, NodeBuilder<>& learned) {
  //TimerStat::CodeTimer codeTimer(d_staticLearningTimer);

  vector<TNode> workList;
  workList.push_back(n);
  std::unordered_set<TNode, TNodeHashFunction> processed;

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
       (n[0][0].getKind() == kind::EQUAL) &&
       (n[0][1].getKind() == kind::EQUAL) &&
       (n[1][0].getKind() == kind::EQUAL) &&
       (n[1][1].getKind() == kind::EQUAL)) {
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
        Node newEquality = a.eqNode(d);
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

bool TheoryUF::areCareDisequal(TNode x, TNode y){
  Assert( d_equalityEngine.hasTerm(x) );
  Assert( d_equalityEngine.hasTerm(y) );
  if( d_equalityEngine.isTriggerTerm(x, THEORY_UF) && d_equalityEngine.isTriggerTerm(y, THEORY_UF) ){
    TNode x_shared = d_equalityEngine.getTriggerTermRepresentative(x, THEORY_UF);
    TNode y_shared = d_equalityEngine.getTriggerTermRepresentative(y, THEORY_UF);
    EqualityStatus eqStatus = d_valuation.getEqualityStatus(x_shared, y_shared);
    if( eqStatus==EQUALITY_FALSE_AND_PROPAGATED || eqStatus==EQUALITY_FALSE || eqStatus==EQUALITY_FALSE_IN_MODEL ){
      return true;
    }
  }
  return false;
}

//TODO: move quantifiers::TermArgTrie to src/theory/
void TheoryUF::addCarePairs( quantifiers::TermArgTrie * t1, quantifiers::TermArgTrie * t2, unsigned arity, unsigned depth ){
  if( depth==arity ){
    if( t2!=NULL ){
      Node f1 = t1->getNodeData();
      Node f2 = t2->getNodeData();
      if( !d_equalityEngine.areEqual( f1, f2 ) ){
        Debug("uf::sharing") << "TheoryUf::computeCareGraph(): checking function " << f1 << " and " << f2 << std::endl;
        vector< pair<TNode, TNode> > currentPairs;
        unsigned arg_start_index = getArgumentStartIndexForApplyTerm( f1 );
        for (unsigned k = arg_start_index; k < f1.getNumChildren(); ++ k) {
          TNode x = f1[k];
          TNode y = f2[k];
          Assert( d_equalityEngine.hasTerm(x) );
          Assert( d_equalityEngine.hasTerm(y) );
          Assert( !d_equalityEngine.areDisequal( x, y, false ) );
          Assert( !areCareDisequal( x, y ) );
          if( !d_equalityEngine.areEqual( x, y ) ){
            if( d_equalityEngine.isTriggerTerm(x, THEORY_UF) && d_equalityEngine.isTriggerTerm(y, THEORY_UF) ){
              TNode x_shared = d_equalityEngine.getTriggerTermRepresentative(x, THEORY_UF);
              TNode y_shared = d_equalityEngine.getTriggerTermRepresentative(y, THEORY_UF);
              currentPairs.push_back(make_pair(x_shared, y_shared));
            }
          }
        }
        for (unsigned c = 0; c < currentPairs.size(); ++ c) {
          Debug("uf::sharing") << "TheoryUf::computeCareGraph(): adding to care-graph" << std::endl;
          addCarePair(currentPairs[c].first, currentPairs[c].second);
        }
      }
    }
  }else{
    if( t2==NULL ){
      if( depth<(arity-1) ){
        //add care pairs internal to each child
        for( std::map< TNode, quantifiers::TermArgTrie >::iterator it = t1->d_data.begin(); it != t1->d_data.end(); ++it ){
          addCarePairs( &it->second, NULL, arity, depth+1 );
        }
      }
      //add care pairs based on each pair of non-disequal arguments
      for( std::map< TNode, quantifiers::TermArgTrie >::iterator it = t1->d_data.begin(); it != t1->d_data.end(); ++it ){
        std::map< TNode, quantifiers::TermArgTrie >::iterator it2 = it;
        ++it2;
        for( ; it2 != t1->d_data.end(); ++it2 ){
          if( !d_equalityEngine.areDisequal(it->first, it2->first, false) ){
            if( !areCareDisequal(it->first, it2->first) ){
              addCarePairs( &it->second, &it2->second, arity, depth+1 );
            }
          }
        }
      }
    }else{
      //add care pairs based on product of indices, non-disequal arguments
      for( std::map< TNode, quantifiers::TermArgTrie >::iterator it = t1->d_data.begin(); it != t1->d_data.end(); ++it ){
        for( std::map< TNode, quantifiers::TermArgTrie >::iterator it2 = t2->d_data.begin(); it2 != t2->d_data.end(); ++it2 ){
          if( !d_equalityEngine.areDisequal(it->first, it2->first, false) ){
            if( !areCareDisequal(it->first, it2->first) ){
              addCarePairs( &it->second, &it2->second, arity, depth+1 );
            }
          }
        }
      }
    }
  }
}

void TheoryUF::computeCareGraph() {

  if (d_sharedTerms.size() > 0) {
    //use term indexing
    Debug("uf::sharing") << "TheoryUf::computeCareGraph(): Build term indices..." << std::endl;
    std::map< Node, quantifiers::TermArgTrie > index;
    std::map< Node, unsigned > arity;
    unsigned functionTerms = d_functionsTerms.size();
    for (unsigned i = 0; i < functionTerms; ++ i) {
      TNode f1 = d_functionsTerms[i];
      Node op = getOperatorForApplyTerm( f1 );
      unsigned arg_start_index = getArgumentStartIndexForApplyTerm( f1 );
      std::vector< TNode > reps;
      bool has_trigger_arg = false;
      for( unsigned j=arg_start_index; j<f1.getNumChildren(); j++ ){
        reps.push_back( d_equalityEngine.getRepresentative( f1[j] ) );
        if( d_equalityEngine.isTriggerTerm( f1[j], THEORY_UF ) ){
          has_trigger_arg = true;
        }
      }
      if( has_trigger_arg ){
        index[op].addTerm( f1, reps, arg_start_index );
        arity[op] = reps.size();
      }
    }
    //for each index
    for( std::map< Node, quantifiers::TermArgTrie >::iterator itii = index.begin(); itii != index.end(); ++itii ){
      Debug("uf::sharing") << "TheoryUf::computeCareGraph(): Process index " << itii->first << "..." << std::endl;
      addCarePairs( &itii->second, NULL, arity[ itii->first ], 0 );
    }
    Debug("uf::sharing") << "TheoryUf::computeCareGraph(): finished." << std::endl;
  }
}/* TheoryUF::computeCareGraph() */

void TheoryUF::conflict(TNode a, TNode b) {
  std::shared_ptr<eq::EqProof> pf =
      d_proofsEnabled ? std::make_shared<eq::EqProof>() : nullptr;
  d_conflictNode = explain(a.eqNode(b), pf.get());
  std::unique_ptr<ProofUF> puf(d_proofsEnabled ? new ProofUF(pf) : nullptr);
  d_out->conflict(d_conflictNode, std::move(puf));
  d_conflict = true;
}

void TheoryUF::eqNotifyNewClass(TNode t) {
  if (d_thss != NULL) {
    d_thss->newEqClass(t);
  }
}

void TheoryUF::eqNotifyPreMerge(TNode t1, TNode t2) {
  //if (getLogicInfo().isQuantified()) {
    //getQuantifiersEngine()->getEfficientEMatcher()->merge( t1, t2 );
  //}
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

unsigned TheoryUF::applyExtensionality(TNode deq) {
  Assert( deq.getKind()==kind::NOT && deq[0].getKind()==kind::EQUAL );
  Assert( deq[0][0].getType().isFunction() );
  // apply extensionality
  if( d_extensionality_deq.find( deq )==d_extensionality_deq.end() ){
    d_extensionality_deq.insert( deq );
    TypeNode tn = deq[0][0].getType();
    std::vector< Node > skolems;
    for( unsigned i=0; i<tn.getNumChildren()-1; i++ ){
      Node k = NodeManager::currentNM()->mkSkolem( "k", tn[i], "skolem created for extensionality." );
      skolems.push_back( k );
    }
    Node t[2];
    for( unsigned i=0; i<2; i++ ){
      std::vector< Node > children;
      Node curr = deq[0][i];
      while( curr.getKind()==kind::HO_APPLY ){
        children.push_back( curr[1] );
        curr = curr[0];
      }
      children.push_back( curr );
      std::reverse( children.begin(), children.end() );
      children.insert( children.end(), skolems.begin(), skolems.end() );
      t[i] = NodeManager::currentNM()->mkNode( kind::APPLY_UF, children );
    }
    Node conc = t[0].eqNode( t[1] ).negate();
    Node lem = NodeManager::currentNM()->mkNode( kind::OR, deq[0], conc );
    Trace("uf-ho-lemma") << "uf-ho-lemma : extensionality : " << lem << std::endl;
    d_out->lemma( lem );
    return 1;
  }else{
    return 0;
  }
}

unsigned TheoryUF::checkExtensionality() {
  unsigned num_lemmas = 0;
  Trace("uf-ho") << "TheoryUF::checkExtensionality..." << std::endl;
  // This is bit eager: we should allow functions to be neither equal nor disequal during model construction
  // However, doing so would require a function-type enumerator.
  std::map< TypeNode, std::vector< Node > > func_eqcs;

  eq::EqClassesIterator eqcs_i = eq::EqClassesIterator( &d_equalityEngine );
  while( !eqcs_i.isFinished() ){
    Node eqc = (*eqcs_i);
    TypeNode tn = eqc.getType();
    if( tn.isFunction() ){
      func_eqcs[tn].push_back( eqc );
      Trace("uf-ho-debug") << "  func eqc : " << tn << " : " << eqc << std::endl;
    }
    ++eqcs_i;
  }
  
  for( std::map< TypeNode, std::vector< Node > >::iterator itf = func_eqcs.begin(); 
       itf != func_eqcs.end(); ++itf ){
    for( unsigned j=0; j<itf->second.size(); j++ ){
      for( unsigned k=(j+1); k<itf->second.size(); k++ ){ 
        // if these equivalence classes are not explicitly disequal, do extensionality to ensure distinctness
        if( !d_equalityEngine.areDisequal( itf->second[j], itf->second[k], false ) ){
          Node deq = Rewriter::rewrite( itf->second[j].eqNode( itf->second[k] ).negate() );
          num_lemmas += applyExtensionality( deq );
        }
      }   
    }
  }
  return num_lemmas;
}

unsigned TheoryUF::applyAppCompletion( TNode n ) {
  Assert( n.getKind()==kind::APPLY_UF );

  //must expand into APPLY_HO version if not there already
  Node ret = TheoryUfRewriter::getHoApplyForApplyUf( n );
  if( !d_equalityEngine.hasTerm( ret ) || !d_equalityEngine.areEqual( ret, n ) ){
    Node eq = ret.eqNode( n );
    Trace("uf-ho-lemma") << "uf-ho-lemma : infer, by apply-expand : " << eq << std::endl;
    d_equalityEngine.assertEquality(eq, true, d_true);
    return 1;
  }else{
    Trace("uf-ho-debug") << "    ...already have " << ret << " == " << n << "." << std::endl;
    return 0;
  }
}

unsigned TheoryUF::checkAppCompletion() {
  Trace("uf-ho") << "TheoryUF::checkApplyCompletion..." << std::endl;
  // compute the operators that are relevant (those for which an HO_APPLY exist)
  std::set< TNode > rlvOp;
  eq::EqClassesIterator eqcs_i = eq::EqClassesIterator( &d_equalityEngine );
  std::map< TNode, std::vector< Node > > apply_uf;
  while( !eqcs_i.isFinished() ){
    Node eqc = (*eqcs_i);
    Trace("uf-ho-debug") << "  apply completion : visit eqc " << eqc << std::endl;
    eq::EqClassIterator eqc_i = eq::EqClassIterator( eqc, &d_equalityEngine );
    while( !eqc_i.isFinished() ){
      Node n = *eqc_i;
      if( n.getKind()==kind::APPLY_UF || n.getKind()==kind::HO_APPLY ){
        int curr_sum = 0;
        std::map< TNode, bool > curr_rops;
        if( n.getKind()==kind::APPLY_UF ){
          TNode rop = d_equalityEngine.getRepresentative( n.getOperator() );
          if( rlvOp.find( rop )!=rlvOp.end() ){
            // try if its operator is relevant
            curr_sum = applyAppCompletion( n );
            if( curr_sum>0 ){
              return curr_sum;
            }
          }else{
            // add to pending list
            apply_uf[rop].push_back( n );
          }
          //arguments are also relevant operators  FIXME (github issue #1115)
          for( unsigned k=0; k<n.getNumChildren(); k++ ){
            if( n[k].getType().isFunction() ){
              TNode rop = d_equalityEngine.getRepresentative( n[k] );
              curr_rops[rop] = true;
            }
          }
        }else{
          Assert( n.getKind()==kind::HO_APPLY );
          TNode rop = d_equalityEngine.getRepresentative( n[0] );
          curr_rops[rop] = true;
        }
        for( std::map< TNode, bool >::iterator itc = curr_rops.begin(); itc != curr_rops.end(); ++itc ){
          TNode rop = itc->first;
          if( rlvOp.find( rop )==rlvOp.end() ){
            rlvOp.insert( rop );
            // now, try each pending APPLY_UF for this operator
            std::map< TNode, std::vector< Node > >::iterator itu = apply_uf.find( rop );
            if( itu!=apply_uf.end() ){
              for( unsigned j=0; j<itu->second.size(); j++ ){
                curr_sum = applyAppCompletion( itu->second[j] );
                if( curr_sum>0 ){
                  return curr_sum;
                }
              }
            }
          }
        }
      }
      ++eqc_i;
    }
    ++eqcs_i;
  }
  return 0;
}

unsigned TheoryUF::checkHigherOrder() {
  Trace("uf-ho") << "TheoryUF::checkHigherOrder..." << std::endl;

  // infer new facts based on apply completion until fixed point 
  unsigned num_facts;
  do{
    num_facts = checkAppCompletion();
    if( d_conflict ){
      Trace("uf-ho") << "...conflict during app-completion." << std::endl;
      return 1;  
    }
  }while( num_facts>0 );

  if( options::ufHoExt() ){
    unsigned num_lemmas = 0;

    num_lemmas = checkExtensionality();
    if( num_lemmas>0 ){
      Trace("uf-ho") << "...extensionality returned " << num_lemmas << " lemmas." << std::endl;
      return num_lemmas;
    }
  }

  Trace("uf-ho") << "...finished check higher order." << std::endl;

  return 0;
}

} /* namespace CVC4::theory::uf */
} /* namespace CVC4::theory */
} /* namespace CVC4 */
