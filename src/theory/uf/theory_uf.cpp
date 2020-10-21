/*********************                                                        */
/*! \file theory_uf.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Morgan Deters, Dejan Jovanovic
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
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

#include "expr/node_algorithm.h"
#include "expr/proof_node_manager.h"
#include "options/quantifiers_options.h"
#include "options/smt_options.h"
#include "options/theory_options.h"
#include "options/uf_options.h"
#include "theory/theory_model.h"
#include "theory/type_enumerator.h"
#include "theory/uf/cardinality_extension.h"
#include "theory/uf/ho_extension.h"
#include "theory/uf/theory_uf_rewriter.h"

using namespace std;

namespace CVC4 {
namespace theory {
namespace uf {

/** Constructs a new instance of TheoryUF w.r.t. the provided context.*/
TheoryUF::TheoryUF(context::Context* c,
                   context::UserContext* u,
                   OutputChannel& out,
                   Valuation valuation,
                   const LogicInfo& logicInfo,
                   ProofNodeManager* pnm,
                   std::string instanceName)
    : Theory(THEORY_UF, c, u, out, valuation, logicInfo, pnm, instanceName),
      d_thss(nullptr),
      d_ho(nullptr),
      d_functionsTerms(c),
      d_symb(u, instanceName),
      d_state(c, u, valuation),
      d_im(*this, d_state, pnm),
      d_notify(d_im, *this)
{
  d_true = NodeManager::currentNM()->mkConst( true );

  ProofChecker* pc = pnm != nullptr ? pnm->getChecker() : nullptr;
  if (pc != nullptr)
  {
    d_ufProofChecker.registerTo(pc);
  }
  // indicate we are using the default theory state and inference managers
  d_theoryState = &d_state;
  d_inferManager = &d_im;
}

TheoryUF::~TheoryUF() {
}

TheoryRewriter* TheoryUF::getTheoryRewriter() { return &d_rewriter; }

bool TheoryUF::needsEqualityEngine(EeSetupInfo& esi)
{
  esi.d_notify = &d_notify;
  esi.d_name = d_instanceName + "theory::uf::ee";
  return true;
}

void TheoryUF::finishInit() {
  Assert(d_equalityEngine != nullptr);
  // combined cardinality constraints are not evaluated in getModelValue
  d_valuation.setUnevaluatedKind(kind::COMBINED_CARDINALITY_CONSTRAINT);
  // Initialize the cardinality constraints solver if the logic includes UF,
  // finite model finding is enabled, and it is not disabled by
  // options::ufssMode().
  if (options::finiteModelFind()
      && options::ufssMode() != options::UfssMode::NONE)
  {
    d_thss.reset(new CardinalityExtension(d_state, d_im, this));
  }
  // The kinds we are treating as function application in congruence
  d_equalityEngine->addFunctionKind(kind::APPLY_UF, false, options::ufHo());
  if (options::ufHo())
  {
    d_equalityEngine->addFunctionKind(kind::HO_APPLY);
    d_ho.reset(new HoExtension(d_state, d_im));
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

//--------------------------------- standard check

bool TheoryUF::needsCheckLastEffort()
{
  // last call effort needed if using finite model finding
  return d_thss != nullptr;
}

void TheoryUF::postCheck(Effort level)
{
  if (d_state.isInConflict())
  {
    return;
  }
  // check with the cardinality constraints extension
  if (d_thss != nullptr)
  {
    d_thss->check(level);
  }
  // check with the higher-order extension at full effort
  if (!d_state.isInConflict() && fullEffort(level))
  {
    if (options::ufHo())
    {
      d_ho->check();
    }
  }
}

bool TheoryUF::preNotifyFact(
    TNode atom, bool pol, TNode fact, bool isPrereg, bool isInternal)
{
  if (d_thss != nullptr)
  {
    bool isDecision =
        d_valuation.isSatLiteral(fact) && d_valuation.isDecision(fact);
    d_thss->assertNode(fact, isDecision);
    if (d_state.isInConflict())
    {
      return true;
    }
  }
  if (atom.getKind() == kind::CARDINALITY_CONSTRAINT
      || atom.getKind() == kind::COMBINED_CARDINALITY_CONSTRAINT)
  {
    if (d_thss == nullptr)
    {
      if (!getLogicInfo().hasCardinalityConstraints())
      {
        std::stringstream ss;
        ss << "Cardinality constraint " << atom
           << " was asserted, but the logic does not allow it." << std::endl;
        ss << "Try using a logic containing \"UFC\"." << std::endl;
        throw Exception(ss.str());
      }
      else
      {
        // support for cardinality constraints is not enabled, set incomplete
        d_out->setIncomplete();
      }
    }
    // don't need to assert cardinality constraints if not producing models
    return !options::produceModels();
  }
  return false;
}

void TheoryUF::notifyFact(TNode atom, bool pol, TNode fact, bool isInternal)
{
  if (!d_state.isInConflict() && atom.getKind() == kind::EQUAL)
  {
    if (options::ufHo() && options::ufHoExt())
    {
      if (!pol && !d_state.isInConflict() && atom[0].getType().isFunction())
      {
        // apply extensionality eagerly using the ho extension
        d_ho->applyExtensionality(fact);
      }
    }
  }
}
//--------------------------------- end standard check

TrustNode TheoryUF::expandDefinition(Node node)
{
  Trace("uf-exp-def") << "TheoryUF::expandDefinition: expanding definition : "
                      << node << std::endl;
  if( node.getKind()==kind::HO_APPLY ){
    if( !options::ufHo() ){
      std::stringstream ss;
      ss << "Partial function applications are not supported in default mode, try --uf-ho.";
      throw LogicException(ss.str());
    }
    Node ret = d_ho->expandDefinition(node);
    if (ret != node)
    {
      Trace("uf-exp-def") << "TheoryUF::expandDefinition: higher-order: "
                          << node << " to " << ret << std::endl;
      return TrustNode::mkTrustRewrite(node, ret, nullptr);
    }
  }
  return TrustNode::null();
}

void TheoryUF::preRegisterTerm(TNode node)
{
  Debug("uf") << "TheoryUF::preRegisterTerm(" << node << ")" << std::endl;

  if (d_thss != NULL) {
    d_thss->preRegisterTerm(node);
  }

  // we always use APPLY_UF if not higher-order, HO_APPLY if higher-order
  //Assert( node.getKind()!=kind::APPLY_UF || !options::ufHo() );
  Assert(node.getKind() != kind::HO_APPLY || options::ufHo());

  switch (node.getKind()) {
  case kind::EQUAL:
    // Add the trigger for equality
    d_equalityEngine->addTriggerPredicate(node);
    break;
  case kind::APPLY_UF:
  case kind::HO_APPLY:
    // Maybe it's a predicate
    if (node.getType().isBoolean()) {
      // Get triggered for both equal and dis-equal
      d_equalityEngine->addTriggerPredicate(node);
    } else {
      // Function applications/predicates
      d_equalityEngine->addTerm(node);
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
    d_equalityEngine->addTerm(node);
    break;
  }
}

void TheoryUF::explain(TNode literal, Node& exp)
{
  Debug("uf") << "TheoryUF::explain(" << literal << ")" << std::endl;
  std::vector<TNode> assumptions;
  // Do the work
  bool polarity = literal.getKind() != kind::NOT;
  TNode atom = polarity ? literal : literal[0];
  if (atom.getKind() == kind::EQUAL)
  {
    d_equalityEngine->explainEquality(
        atom[0], atom[1], polarity, assumptions, nullptr);
  }
  else
  {
    d_equalityEngine->explainPredicate(atom, polarity, assumptions, nullptr);
  }
  exp = mkAnd(assumptions);
}

TrustNode TheoryUF::explain(TNode literal) { return d_im.explainLit(literal); }

bool TheoryUF::collectModelValues(TheoryModel* m, const std::set<Node>& termSet)
{
  if( options::ufHo() ){
    // must add extensionality disequalities for all pairs of (non-disequal)
    // function equivalence classes.
    if (!d_ho->collectModelInfoHo(m, termSet))
    {
      Trace("uf") << "Collect model info fail HO" << std::endl;
      return false;
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
      // no proof generator provided
      d_im.lemma(*i);
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

    if (n.isClosure())
    {
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
  if (d_equalityEngine->areEqual(a, b))
  {
    // The terms are implied to be equal
    return EQUALITY_TRUE;
  }

  // Check for disequality
  if (d_equalityEngine->areDisequal(a, b, false))
  {
    // The terms are implied to be dis-equal
    return EQUALITY_FALSE;
  }

  // All other terms we interpret as dis-equal in the model
  return EQUALITY_FALSE_IN_MODEL;
}

bool TheoryUF::areCareDisequal(TNode x, TNode y){
  Assert(d_equalityEngine->hasTerm(x));
  Assert(d_equalityEngine->hasTerm(y));
  if (d_equalityEngine->isTriggerTerm(x, THEORY_UF)
      && d_equalityEngine->isTriggerTerm(y, THEORY_UF))
  {
    TNode x_shared =
        d_equalityEngine->getTriggerTermRepresentative(x, THEORY_UF);
    TNode y_shared =
        d_equalityEngine->getTriggerTermRepresentative(y, THEORY_UF);
    EqualityStatus eqStatus = d_valuation.getEqualityStatus(x_shared, y_shared);
    if( eqStatus==EQUALITY_FALSE_AND_PROPAGATED || eqStatus==EQUALITY_FALSE || eqStatus==EQUALITY_FALSE_IN_MODEL ){
      return true;
    }
  }
  return false;
}

void TheoryUF::addCarePairs(const TNodeTrie* t1,
                            const TNodeTrie* t2,
                            unsigned arity,
                            unsigned depth)
{
  if( depth==arity ){
    if( t2!=NULL ){
      Node f1 = t1->getData();
      Node f2 = t2->getData();
      if (!d_equalityEngine->areEqual(f1, f2))
      {
        Debug("uf::sharing") << "TheoryUf::computeCareGraph(): checking function " << f1 << " and " << f2 << std::endl;
        vector< pair<TNode, TNode> > currentPairs;
        for (size_t k = 0, nchildren = f1.getNumChildren(); k < nchildren; ++k)
        {
          TNode x = f1[k];
          TNode y = f2[k];
          Assert(d_equalityEngine->hasTerm(x));
          Assert(d_equalityEngine->hasTerm(y));
          Assert(!d_equalityEngine->areDisequal(x, y, false));
          Assert(!areCareDisequal(x, y));
          if (!d_equalityEngine->areEqual(x, y))
          {
            if (d_equalityEngine->isTriggerTerm(x, THEORY_UF)
                && d_equalityEngine->isTriggerTerm(y, THEORY_UF))
            {
              TNode x_shared =
                  d_equalityEngine->getTriggerTermRepresentative(x, THEORY_UF);
              TNode y_shared =
                  d_equalityEngine->getTriggerTermRepresentative(y, THEORY_UF);
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
        for (const std::pair<const TNode, TNodeTrie>& tt : t1->d_data)
        {
          addCarePairs(&tt.second, NULL, arity, depth + 1);
        }
      }
      //add care pairs based on each pair of non-disequal arguments
      for (std::map<TNode, TNodeTrie>::const_iterator it = t1->d_data.begin();
           it != t1->d_data.end();
           ++it)
      {
        std::map<TNode, TNodeTrie>::const_iterator it2 = it;
        ++it2;
        for( ; it2 != t1->d_data.end(); ++it2 ){
          if (!d_equalityEngine->areDisequal(it->first, it2->first, false))
          {
            if( !areCareDisequal(it->first, it2->first) ){
              addCarePairs( &it->second, &it2->second, arity, depth+1 );
            }
          }
        }
      }
    }else{
      //add care pairs based on product of indices, non-disequal arguments
      for (const std::pair<const TNode, TNodeTrie>& tt1 : t1->d_data)
      {
        for (const std::pair<const TNode, TNodeTrie>& tt2 : t2->d_data)
        {
          if (!d_equalityEngine->areDisequal(tt1.first, tt2.first, false))
          {
            if (!areCareDisequal(tt1.first, tt2.first))
            {
              addCarePairs(&tt1.second, &tt2.second, arity, depth + 1);
            }
          }
        }
      }
    }
  }
}

void TheoryUF::computeCareGraph() {
  if (d_sharedTerms.empty())
  {
    return;
  }
  // Use term indexing. We build separate indices for APPLY_UF and HO_APPLY.
  // We maintain indices per operator for the former, and indices per
  // function type for the latter.
  Debug("uf::sharing") << "TheoryUf::computeCareGraph(): Build term indices..."
                       << std::endl;
  std::map<Node, TNodeTrie> index;
  std::map<TypeNode, TNodeTrie> hoIndex;
  std::map<Node, size_t> arity;
  for (TNode app : d_functionsTerms)
  {
    std::vector<TNode> reps;
    bool has_trigger_arg = false;
    for (const Node& j : app)
    {
      reps.push_back(d_equalityEngine->getRepresentative(j));
      if (d_equalityEngine->isTriggerTerm(j, THEORY_UF))
      {
        has_trigger_arg = true;
      }
    }
    if (has_trigger_arg)
    {
      if (app.getKind() == kind::APPLY_UF)
      {
        Node op = app.getOperator();
        index[op].addTerm(app, reps);
        arity[op] = reps.size();
      }
      else
      {
        Assert(app.getKind() == kind::HO_APPLY);
        // add it to the hoIndex for the function type
        hoIndex[app[0].getType()].addTerm(app, reps);
      }
    }
  }
  // for each index
  for (std::pair<const Node, TNodeTrie>& tt : index)
  {
    Debug("uf::sharing") << "TheoryUf::computeCareGraph(): Process index "
                         << tt.first << "..." << std::endl;
    Assert(arity.find(tt.first) != arity.end());
    addCarePairs(&tt.second, nullptr, arity[tt.first], 0);
  }
  for (std::pair<const TypeNode, TNodeTrie>& tt : hoIndex)
  {
    Debug("uf::sharing") << "TheoryUf::computeCareGraph(): Process ho index "
                         << tt.first << "..." << std::endl;
    // the arity of HO_APPLY is always two
    addCarePairs(&tt.second, nullptr, 2, 0);
  }
  Debug("uf::sharing") << "TheoryUf::computeCareGraph(): finished."
                       << std::endl;
}/* TheoryUF::computeCareGraph() */

void TheoryUF::eqNotifyNewClass(TNode t) {
  if (d_thss != NULL) {
    d_thss->newEqClass(t);
  }
}

void TheoryUF::eqNotifyMerge(TNode t1, TNode t2)
{
  if (d_thss != NULL) {
    d_thss->merge(t1, t2);
  }
}

void TheoryUF::eqNotifyDisequal(TNode t1, TNode t2, TNode reason) {
  if (d_thss != NULL) {
    d_thss->assertDisequal(t1, t2, reason);
  }
}

} /* namespace CVC4::theory::uf */
} /* namespace CVC4::theory */
} /* namespace CVC4 */
