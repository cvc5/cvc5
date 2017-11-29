/*********************                                                        */
/*! \file term_formula_removal.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Morgan Deters, Dejan Jovanovic
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2017 by the authors listed in the file AUTHORS
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

#include "options/proof_options.h"
#include "proof/proof_manager.h"
#include "theory/ite_utilities.h"

using namespace std;

namespace CVC4 {

RemoveTermFormulas::RemoveTermFormulas(context::UserContext* u)
    : d_tfCache(u), d_skolem_cache(u)
{
  d_containsVisitor = new theory::ContainsTermITEVisitor();
}

RemoveTermFormulas::~RemoveTermFormulas(){
  delete d_containsVisitor;
}

void RemoveTermFormulas::garbageCollect(){
  d_containsVisitor->garbageCollect();
}

theory::ContainsTermITEVisitor* RemoveTermFormulas::getContainsVisitor() {
  return d_containsVisitor;
}

void RemoveTermFormulas::run(std::vector<Node>& output, IteSkolemMap& iteSkolemMap, bool reportDeps)
{
  size_t n = output.size();
  for (unsigned i = 0, i_end = output.size(); i < i_end; ++ i) {
    // Do this in two steps to avoid Node problems(?)
    // Appears related to bug 512, splitting this into two lines
    // fixes the bug on clang on Mac OS
    Node itesRemoved = run(output[i], output, iteSkolemMap, false, false);
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

bool RemoveTermFormulas::containsTermITE(TNode e) const {
  return d_containsVisitor->containsTermITE(e);
}

Node RemoveTermFormulas::run(TNode node, std::vector<Node>& output,
                    IteSkolemMap& iteSkolemMap, bool inQuant, bool inTerm) {
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
  if(node.getKind() == kind::ITE) {
    // If an ITE, replace it
    if (!nodeType.isBoolean() && (!inQuant || !node.hasBoundVar()))
    {
      skolem = getSkolemForNode(node);
      if (skolem.isNull())
      {
        // Make the skolem to represent the ITE
        skolem = nodeManager->mkSkolem(
            "termITE",
            nodeType,
            "a variable introduced due to term-level ITE removal");
        d_skolem_cache.insert(node, skolem);

        // The new assertion
        newAssertion = nodeManager->mkNode(
            kind::ITE, node[0], skolem.eqNode(node[1]), skolem.eqNode(node[2]));
      }
    }
  }
  else if (node.getKind() == kind::LAMBDA)
  {
    // if a lambda, do lambda-lifting
    if (!inQuant)
    {
      skolem = getSkolemForNode(node);
      if (skolem.isNull())
      {
        // Make the skolem to represent the lambda
        skolem = nodeManager->mkSkolem(
            "lambdaF",
            nodeType,
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
      }
    }
  }
  else if (node.getKind() == kind::CHOICE)
  {
    // If a Hilbert choice function, witness the choice.
    //   For details on this operator, see
    //   http://planetmath.org/hilbertsvarepsilonoperator.
    if (!inQuant)
    {
      skolem = getSkolemForNode(node);
      if (skolem.isNull())
      {
        // Make the skolem to witness the choice
        skolem = nodeManager->mkSkolem(
            "choiceK",
            nodeType,
            "a skolem introduced due to term-level Hilbert choice removal");
        d_skolem_cache.insert(node, skolem);

        Assert(node[0].getNumChildren() == 1);

        // The new assertion is the assumption that the body
        // of the choice operator holds for the Skolem
        newAssertion = node[1].substitute(node[0][0], skolem);
      }
    }
  }
  else if (node.getKind() != kind::BOOLEAN_TERM_VARIABLE && nodeType.isBoolean()
           && inTerm
           && !inQuant)
  {
    // if a non-variable Boolean term, replace it
    skolem = getSkolemForNode(node);
    if (skolem.isNull())
    {
      // Make the skolem to represent the Boolean term
      // skolem = nodeManager->mkSkolem("termBT", nodeType, "a variable
      // introduced due to Boolean term removal");
      skolem = nodeManager->mkBooleanTermVariable();
      d_skolem_cache.insert(node, skolem);

      // The new assertion
      newAssertion = skolem.eqNode(node);
    }
  }

  // if the term should be replaced by a skolem
  if( !skolem.isNull() ){
    // Attach the skolem
    d_tfCache.insert(cacheKey, skolem);

    // if the skolem was introduced in this call
    if (!newAssertion.isNull())
    {
      Debug("ite") << "*** term formula removal introduced " << skolem
                   << " for " << node << std::endl;

      // Remove ITEs from the new assertion, rewrite it and push it to the
      // output
      newAssertion = run(newAssertion, output, iteSkolemMap, false, false);

      iteSkolemMap[skolem] = output.size();
      output.push_back(newAssertion);
    }

    // The representation is now the skolem
    return skolem;
  }
  
  if(node.getKind() == kind::FORALL || node.getKind() == kind::EXISTS) {
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
    Node newChild = run(*it, output, iteSkolemMap, inQuant, inTerm);
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

  if(node.getKind() == kind::FORALL || node.getKind() == kind::EXISTS) {
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

}/* CVC4 namespace */
