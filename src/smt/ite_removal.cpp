/*********************                                                        */
/*! \file ite_removal.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Morgan Deters, Dejan Jovanovic, Tim King
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2016 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Removal of term ITEs
 **
 ** Removal of term ITEs.
 **/
#include "smt/ite_removal.h"

#include <vector>

#include "options/proof_options.h"
#include "proof/proof_manager.h"
#include "theory/ite_utilities.h"

using namespace std;

namespace CVC4 {

RemoveITE::RemoveITE(context::UserContext* u)
  : d_iteCache(u)
{
  d_containsVisitor = new theory::ContainsTermITEVisitor();
}

RemoveITE::~RemoveITE(){
  delete d_containsVisitor;
}

void RemoveITE::garbageCollect(){
  d_containsVisitor->garbageCollect();
}

theory::ContainsTermITEVisitor* RemoveITE::getContainsVisitor() {
  return d_containsVisitor;
}

size_t RemoveITE::collectedCacheSizes() const{
  return d_containsVisitor->cache_size() + d_iteCache.size();
}

void RemoveITE::run(std::vector<Node>& output, IteSkolemMap& iteSkolemMap, bool reportDeps)
{
  size_t n = output.size();
  for (unsigned i = 0, i_end = output.size(); i < i_end; ++ i) {
    // Do this in two steps to avoid Node problems(?)
    // Appears related to bug 512, splitting this into two lines
    // fixes the bug on clang on Mac OS
    Node itesRemoved = run(output[i], output, iteSkolemMap, false);
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

bool RemoveITE::containsTermITE(TNode e) const {
  return d_containsVisitor->containsTermITE(e);
}

Node RemoveITE::run(TNode node, std::vector<Node>& output,
                    IteSkolemMap& iteSkolemMap, bool inQuant) {
  // Current node
  Debug("ite") << "removeITEs(" << node << ")" << endl;

  if(node.isVar() || node.isConst() ||
     (options::biasedITERemoval() && !containsTermITE(node))){
    return Node(node);
  }

  // The result may be cached already
  std::pair<Node, bool> cacheKey(node, inQuant);
  NodeManager *nodeManager = NodeManager::currentNM();
  ITECache::const_iterator i = d_iteCache.find(cacheKey);
  if(i != d_iteCache.end()) {
    Node cached = (*i).second;
    Debug("ite") << "removeITEs: in-cache: " << cached << endl;
    return cached.isNull() ? Node(node) : cached;
  }

  // Remember that we're inside a quantifier
  if(node.getKind() == kind::FORALL || node.getKind() == kind::EXISTS) {
    inQuant = true;
  }

  // If an ITE replace it
  if(node.getKind() == kind::ITE) {
    TypeNode nodeType = node.getType();
    if(!nodeType.isBoolean() && (!inQuant || !node.hasBoundVar())) {
      Node skolem;
      // Make the skolem to represent the ITE
      skolem = nodeManager->mkSkolem("termITE", nodeType, "a variable introduced due to term-level ITE removal");

      // The new assertion
      Node newAssertion =
        nodeManager->mkNode(kind::ITE, node[0], skolem.eqNode(node[1]),
                            skolem.eqNode(node[2]));
      Debug("ite") << "removeITEs(" << node << ") => " << newAssertion << endl;

      // Attach the skolem
      d_iteCache.insert(cacheKey, skolem);

      // Remove ITEs from the new assertion, rewrite it and push it to the output
      newAssertion = run(newAssertion, output, iteSkolemMap, inQuant);

      iteSkolemMap[skolem] = output.size();
      output.push_back(newAssertion);

      // The representation is now the skolem
      return skolem;
    }
  }

  // If not an ITE, go deep
  vector<Node> newChildren;
  bool somethingChanged = false;
  if(node.getMetaKind() == kind::metakind::PARAMETERIZED) {
    newChildren.push_back(node.getOperator());
  }
  // Remove the ITEs from the children
  for(TNode::const_iterator it = node.begin(), end = node.end(); it != end; ++it) {
    Node newChild = run(*it, output, iteSkolemMap, inQuant);
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

Node RemoveITE::replace(TNode node, bool inQuant) const {
  if(node.isVar() || node.isConst() ||
     (options::biasedITERemoval() && !containsTermITE(node))){
    return Node(node);
  }

  // Check the cache
  NodeManager *nodeManager = NodeManager::currentNM();
  ITECache::const_iterator i = d_iteCache.find(make_pair(node, inQuant));
  if(i != d_iteCache.end()) {
    Node cached = (*i).second;
    return cached.isNull() ? Node(node) : cached;
  }

  // Remember that we're inside a quantifier
  if(node.getKind() == kind::FORALL || node.getKind() == kind::EXISTS) {
    inQuant = true;
  }

  vector<Node> newChildren;
  bool somethingChanged = false;
  if(node.getMetaKind() == kind::metakind::PARAMETERIZED) {
    newChildren.push_back(node.getOperator());
  }
  // Replace in children
  for(TNode::const_iterator it = node.begin(), end = node.end(); it != end; ++it) {
    Node newChild = replace(*it, inQuant);
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

}/* CVC4 namespace */
