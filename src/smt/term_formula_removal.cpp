/*********************                                                        */
/*! \file term_formula_removal.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Dejan Jovanovic, Morgan Deters
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Removal of term formulas
 **
 ** Removal of term formulas.
 **/
#include "smt/term_formula_removal.h"

#include <vector>

#include "expr/node_algorithm.h"
#include "expr/skolem_manager.h"
#include "options/proof_options.h"
#include "proof/proof_manager.h"

using namespace std;

namespace CVC4 {

RemoveTermFormulas::RemoveTermFormulas(context::UserContext* u)
    : d_tfCache(u), d_skolem_cache(u), d_tpg(nullptr)
{
}

RemoveTermFormulas::~RemoveTermFormulas() {}

void RemoveTermFormulas::run(std::vector<Node>& output,
                             IteSkolemMap& iteSkolemMap,
                             bool reportDeps,
                             LazyCDProof* lp)
{
  if (lp!=nullptr)
  {
    // create the proof generator if not already done so
    if (d_tpg==nullptr)
    {
      // use the proof manager of the given proof
      d_tpg.reset(new theory::EagerProofGenerator(lp->getManager()));
    }
  }
  size_t n = output.size();
  for (unsigned i = 0, i_end = output.size(); i < i_end; ++ i) {
    // Do this in two steps to avoid Node problems(?)
    // Appears related to bug 512, splitting this into two lines
    // fixes the bug on clang on Mac OS
    Node itesRemoved = run(output[i], output, iteSkolemMap, false, false, lp);
    // In some calling contexts, not necessary to report dependence information.
    if (reportDeps &&
        (options::unsatCores() || options::fewerPreprocessingHoles())) {
      // new assertions have a dependence on the node
      PROOF( ProofManager::currentPM()->addDependence(itesRemoved, output[i]); )
      while(n < output.size()) {
        PROOF( ProofManager::currentPM()->addDependence(output[n], output[i]); )
        ++n;
      }
    }
    output[i] = itesRemoved;
  }
}

Node RemoveTermFormulas::run(TNode node,
                             std::vector<Node>& output,
                             IteSkolemMap& iteSkolemMap,
                             bool inQuant,
                             bool inTerm,
                             LazyCDProof* lp)
{
  // Current node
  Debug("ite") << "removeITEs(" << node << ")" << " " << inQuant << " " << inTerm << endl;

  //if(node.isVar() || node.isConst()){
  //   (options::biasedITERemoval() && !containsTermITE(node))){
  //if(node.isVar()){
  //  return Node(node);
  //}
  if( node.getKind()==kind::INST_PATTERN_LIST ){
    return Node(node);
  }

  // The result may be cached already
  int cv = cacheVal( inQuant, inTerm );
  std::pair<Node, int> cacheKey(node, cv);
  NodeManager *nodeManager = NodeManager::currentNM();
  TermFormulaCache::const_iterator i = d_tfCache.find(cacheKey);
  if (i != d_tfCache.end())
  {
    Node cached = (*i).second;
    Debug("ite") << "removeITEs: in-cache: " << cached << endl;
    return cached.isNull() ? Node(node) : cached;
  }


  TypeNode nodeType = node.getType();
  Node skolem;
  Node newAssertion;
  // the exists form of the assertion
  Node existsAssertion;
  ProofGenerator* newAssertionPg = nullptr;
  // Handle non-Boolean ITEs here. Boolean ones (within terms) are handled
  // in the "non-variable Boolean term within term" case below.
  if (node.getKind() == kind::ITE && !nodeType.isBoolean())
  {
    // Here, we eliminate the ITE if we are not Boolean and if we do not contain
    // a free variable.
    if (!inQuant || !expr::hasFreeVar(node))
    {
      skolem = getSkolemForNode(node);
      if (skolem.isNull())
      {
        // Make the skolem to represent the ITE
        SkolemManager* sm = nodeManager->getSkolemManager();
        skolem = sm->mkPurifySkolem(
            node,
            "termITE",
            "a variable introduced due to term-level ITE removal");
        d_skolem_cache.insert(node, skolem);

        // The new assertion
        newAssertion = nodeManager->mkNode(
            kind::ITE, node[0], skolem.eqNode(node[1]), skolem.eqNode(node[2]));

        // we justify it internally
        if (lp != nullptr)
        {
          // --------------------------------------- REMOVE_TERM_FORMULA_AXIOM
          // (ite node[0] (= node node[1]) (= node node[2]))
          // ----------------------------------------- EXISTS_INTRO
          // (exists ((x T)) (ite node[0] (= x node[1]) (= x node[2])))
          std::vector<Node> pfChildren;
          std::vector<Node> pfArgs;
          pfArgs.push_back(node);
          Node conc = getAxiomFor(node);
          CDProof cdp(lp->getManager());
          cdp.addStep(conc, PfRule::REMOVE_TERM_FORMULA_AXIOM, pfChildren, pfArgs);
          existsAssertion = sm->mkExistential(node,conc);
          pfChildren.push_back(conc);
          cdp.addStep(existsAssertion, PfRule::EXISTS_INTRO, pfChildren, pfArgs);
          Assert (d_tpg!=nullptr);
          // store it in the proof generator managed by this class
          d_tpg->setProofFor(existsAssertion, cdp.mkProof(existsAssertion));
          newAssertionPg = d_tpg.get();
        }
      }
    }
  }
  else if (node.getKind() == kind::LAMBDA)
  {
    // if a lambda, do lambda-lifting
    if (!inQuant || !expr::hasFreeVar(node))
    {
      skolem = getSkolemForNode(node);
      if (skolem.isNull())
      {
        // Make the skolem to represent the lambda
        SkolemManager* sm = nodeManager->getSkolemManager();
        skolem = sm->mkPurifySkolem(
            node,
            "lambdaF",
            "a function introduced due to term-level lambda removal");
        d_skolem_cache.insert(node, skolem);

        // The new assertion
        std::vector<Node> children;
        // bound variable list
        children.push_back(node[0]);
        // body
        std::vector<Node> skolem_app_c;
        skolem_app_c.push_back(skolem);
        skolem_app_c.insert(skolem_app_c.end(), node[0].begin(), node[0].end());
        Node skolem_app = nodeManager->mkNode(kind::APPLY_UF, skolem_app_c);
        children.push_back(skolem_app.eqNode(node[1]));
        // axiom defining skolem
        newAssertion = nodeManager->mkNode(kind::FORALL, children);

        // lambda lifting is trivial to justify, hence we don't set a proof
        // generator here
      }
    }
  }
  else if (node.getKind() == kind::WITNESS)
  {
    // If a witness choice
    //   For details on this operator, see
    //   http://planetmath.org/hilbertsvarepsilonoperator.
    if (!inQuant || !expr::hasFreeVar(node))
    {
      // TODO: we can replace by t if body is of the form (and (= z t) ...)
      skolem = getSkolemForNode(node);
      if (skolem.isNull())
      {
        // Make the skolem to witness the choice, which notice is handled
        // as a special case within SkolemManager::mkPurifySkolem.
        SkolemManager* sm = nodeManager->getSkolemManager();
        skolem = sm->mkPurifySkolem(
            node,
            "witnessK",
            "a skolem introduced due to term-level witness removal");
        d_skolem_cache.insert(node, skolem);

        Assert(node[0].getNumChildren() == 1);

        // The new assertion is the assumption that the body
        // of the witness operator holds for the Skolem
        newAssertion = node[1].substitute(node[0][0], skolem);

        // Get the proof generator if one exists, which was responsible for
        // constructing this witness term. This may not exist, in which case
        // the witness term was trivial to justify. This is the case e.g. for
        // purification witness terms.
        if (lp != nullptr)
        {
          existsAssertion = nodeManager->mkNode(kind::EXISTS, node[0], node[1]);
          newAssertionPg = sm->getProofGenerator(existsAssertion);
        }
      }
    }
  }
  else if (node.getKind() != kind::BOOLEAN_TERM_VARIABLE && nodeType.isBoolean()
           && inTerm
           && !inQuant)
  {
    // if a non-variable Boolean term within another term, replace it
    skolem = getSkolemForNode(node);
    if (skolem.isNull())
    {
      // Make the skolem to represent the Boolean term
      // Skolems introduced for Boolean formulas appearing in terms have a
      // special kind (BOOLEAN_TERM_VARIABLE) that ensures they are handled
      // properly in theory combination. We must use this kind here instead of a
      // generic skolem. Notice that the name/comment are currently ignored
      // within SkolemManager::mkPurifySkolem, since BOOLEAN_TERM_VARIABLE
      // variables cannot be given names.
      SkolemManager* sm = nodeManager->getSkolemManager();
      skolem = sm->mkPurifySkolem(
          node,
          "btvK",
          "a Boolean term variable introduced during term formula removal",
          NodeManager::SKOLEM_BOOL_TERM_VAR);
      d_skolem_cache.insert(node, skolem);

      // The new assertion
      newAssertion = skolem.eqNode(node);

      // Boolean term removal is trivial to justify, hence we don't set a proof
      // generator here
    }
  }

  // if the term should be replaced by a skolem
  if( !skolem.isNull() ){
    // Attach the skolem
    d_tfCache.insert(cacheKey, skolem);

    // if the skolem was introduced in this call
    if (!newAssertion.isNull())
    {
      if (lp != nullptr)
      {
        std::vector<Node> pfChildren;
        std::vector<Node> pfArgs;
        // justify it
        if (newAssertionPg != nullptr)
        {
          // ------------------- from skolem manager
          // (exists x. P[x])
          // ------------------- SKOLEMIZE
          // P[ witness x. P[x] ]
          // where the latter conclusion should be the witness form of
          // newAssertion.
          // the existential is proven lazily by the provided proof generator
          lp->addLazyStep(existsAssertion, newAssertionPg);
          // the skolemized form is proven as a step
          pfChildren.push_back(existsAssertion);
          lp->addStep(newAssertion, PfRule::SKOLEMIZE, pfChildren, pfArgs);
        }
        else
        {
          // otherwise should have trivial justification
          pfArgs.push_back(newAssertion);
          // ---------------- MACRO_SR_PRED_INTRO
          // newAssertion
          lp->addStep(
              newAssertion, PfRule::MACRO_SR_PRED_INTRO, pfChildren, pfArgs);
        }
      }
      Debug("ite") << "*** term formula removal introduced " << skolem
                   << " for " << node << std::endl;

      // Remove ITEs from the new assertion, rewrite it and push it to the
      // output
      newAssertion = run(newAssertion, output, iteSkolemMap, false, false, lp);

      iteSkolemMap[skolem] = output.size();
      output.push_back(newAssertion);
    }

    // The representation is now the skolem
    return skolem;
  }

  if (node.isClosure())
  {
    // Remember if we're inside a quantifier
    inQuant = true;
  }else if( !inTerm && hasNestedTermChildren( node ) ){
    // Remember if we're inside a term
    Debug("ite") << "In term because of " << node << " " << node.getKind() << std::endl;
    inTerm = true;
  }

  // If not an ITE, go deep
  vector<Node> newChildren;
  bool somethingChanged = false;
  if(node.getMetaKind() == kind::metakind::PARAMETERIZED) {
    newChildren.push_back(node.getOperator());
  }
  // Remove the ITEs from the children
  for(TNode::const_iterator it = node.begin(), end = node.end(); it != end; ++it) {
    Node newChild = run(*it, output, iteSkolemMap, inQuant, inTerm, lp);
    somethingChanged |= (newChild != *it);
    newChildren.push_back(newChild);
  }

  // If changes, we rewrite
  if(somethingChanged) {
    Node cached = nodeManager->mkNode(node.getKind(), newChildren);
    d_tfCache.insert(cacheKey, cached);
    return cached;
  } else {
    d_tfCache.insert(cacheKey, Node::null());
    return node;
  }
}

Node RemoveTermFormulas::getSkolemForNode(Node node) const
{
  context::CDInsertHashMap<Node, Node, NodeHashFunction>::const_iterator itk =
      d_skolem_cache.find(node);
  if (itk != d_skolem_cache.end())
  {
    return itk->second;
  }
  return Node::null();
}

Node RemoveTermFormulas::replace(TNode node, bool inQuant, bool inTerm) const {
  if( node.getKind()==kind::INST_PATTERN_LIST ){
    return Node(node);
  }

  // Check the cache
  NodeManager *nodeManager = NodeManager::currentNM();
  int cv = cacheVal( inQuant, inTerm );
  TermFormulaCache::const_iterator i = d_tfCache.find(make_pair(node, cv));
  if (i != d_tfCache.end())
  {
    Node cached = (*i).second;
    return cached.isNull() ? Node(node) : cached;
  }

  if (node.isClosure())
  {
    // Remember if we're inside a quantifier
    inQuant = true;
  }else if( !inTerm && hasNestedTermChildren( node ) ){
    // Remember if we're inside a term
    inTerm = true;
  }  

  vector<Node> newChildren;
  bool somethingChanged = false;
  if(node.getMetaKind() == kind::metakind::PARAMETERIZED) {
    newChildren.push_back(node.getOperator());
  }
  // Replace in children
  for(TNode::const_iterator it = node.begin(), end = node.end(); it != end; ++it) {
    Node newChild = replace(*it, inQuant, inTerm);
    somethingChanged |= (newChild != *it);
    newChildren.push_back(newChild);
  }

  // If changes, we rewrite
  if(somethingChanged) {
    return nodeManager->mkNode(node.getKind(), newChildren);
  } else {
    return node;
  }
}

// returns true if the children of node should be considered nested terms 
bool RemoveTermFormulas::hasNestedTermChildren( TNode node ) {
  return theory::kindToTheoryId(node.getKind())!=theory::THEORY_BOOL && 
         node.getKind()!=kind::EQUAL && node.getKind()!=kind::SEP_STAR && 
         node.getKind()!=kind::SEP_WAND && node.getKind()!=kind::SEP_LABEL && 
         node.getKind()!=kind::BITVECTOR_EAGER_ATOM;
         // dont' worry about FORALL or EXISTS (handled separately)
}

Node RemoveTermFormulas::getAxiomFor(Node n)
{
  NodeManager * nm = NodeManager::currentNM();
  Kind k = n.getKind();
  if (k==kind::ITE)
  {
    return nm->mkNode(kind::ITE, n[0], n.eqNode(n[1]), n.eqNode(n[2]));
  }
  return Node::null();
}

}/* CVC4 namespace */
