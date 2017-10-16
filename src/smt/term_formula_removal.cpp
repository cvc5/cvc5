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
  : d_iteCache(u)
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

size_t RemoveTermFormulas::collectedCacheSizes() const{
  return d_containsVisitor->cache_size() + d_iteCache.size();
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
  ITECache::const_iterator i = d_iteCache.find(cacheKey);
  if(i != d_iteCache.end()) {
    Node cached = (*i).second;
    Debug("ite") << "removeITEs: in-cache: " << cached << endl;
    return cached.isNull() ? Node(node) : cached;
  }


  // If an ITE, replace it
  TypeNode nodeType = node.getType();
  Node skolem;
  Node newAssertion;
  if(node.getKind() == kind::ITE) {
    if(!nodeType.isBoolean() && (!inQuant || !node.hasBoundVar())) {
      // Make the skolem to represent the ITE
      skolem = nodeManager->mkSkolem("termITE", nodeType, "a variable introduced due to term-level ITE removal");

      // The new assertion
      newAssertion =
        nodeManager->mkNode(kind::ITE, node[0], skolem.eqNode(node[1]),
                            skolem.eqNode(node[2]));
    }
  }
  //if a lambda, do lambda-lifting
  if( node.getKind() == kind::LAMBDA && !inQuant ){
    // Make the skolem to represent the ITE
    skolem = nodeManager->mkSkolem("lambdaF", nodeType, "a function introduced due to term-level lambda removal");

    // The new assertion
    std::vector< Node > children;
    // bound variable list
    children.push_back( node[0] );
    // body
    std::vector< Node > skolem_app_c;
    skolem_app_c.push_back( skolem );
    for( unsigned i=0; i<node[0].getNumChildren(); i++ ){
      skolem_app_c.push_back( node[0][i] );
    }
    Node skolem_app = nodeManager->mkNode( kind::APPLY_UF, skolem_app_c );
    children.push_back( skolem_app.eqNode( node[1] ) );
    // axiom defining skolem
    newAssertion = nodeManager->mkNode( kind::FORALL, children );
  }
  //if a non-variable Boolean term, replace it
  if(node.getKind()!=kind::BOOLEAN_TERM_VARIABLE && nodeType.isBoolean() && inTerm && !inQuant ){//(!inQuant || !node.hasBoundVar())){

    // Make the skolem to represent the Boolean term
    //skolem = nodeManager->mkSkolem("termBT", nodeType, "a variable introduced due to Boolean term removal");
    skolem = nodeManager->mkBooleanTermVariable();

    // The new assertion
    newAssertion = skolem.eqNode( node );
  }

  // if we introduced a skolem
  if( !skolem.isNull() ){
    Debug("ite") << "removeITEs(" << node << ") => " << newAssertion << endl;

    // Attach the skolem
    d_iteCache.insert(cacheKey, skolem);

    // Remove ITEs from the new assertion, rewrite it and push it to the output
    newAssertion = run(newAssertion, output, iteSkolemMap, false, false);

    iteSkolemMap[skolem] = output.size();
    output.push_back(newAssertion);

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
    d_iteCache.insert(cacheKey, cached);
    return cached;
  } else {
    d_iteCache.insert(cacheKey, Node::null());
    return node;
  }
}

Node RemoveTermFormulas::replace(TNode node, bool inQuant, bool inTerm) const {
  //if(node.isVar() || node.isConst()){
  //   (options::biasedITERemoval() && !containsTermITE(node))){
  //if(node.isVar()){
  //  return Node(node);
  //}
  if( node.getKind()==kind::INST_PATTERN_LIST ){
    return Node(node);
  }

  // Check the cache
  NodeManager *nodeManager = NodeManager::currentNM();
  int cv = cacheVal( inQuant, inTerm );
  ITECache::const_iterator i = d_iteCache.find(make_pair(node, cv));
  if(i != d_iteCache.end()) {
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
