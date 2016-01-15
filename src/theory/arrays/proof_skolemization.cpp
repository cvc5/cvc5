/*********************                                                        */
/*! \file proof_skolemization.cpp
 **/

#include "theory/arrays/proof_skolemization.h"

namespace CVC4 {
namespace theory {
namespace arrays {

std::hash_map<Node, Node, NodeHashFunction> ProofSkolemization::d_nodeToSkolem;
std::hash_map<Node, Node, NodeHashFunction> ProofSkolemization::d_skolemToNode;

void ProofSkolemization::registerSkolem(Node ref, Node skolem) {
  Debug("gk::proof") << "ProofSkolemization: registerSkolem: ref = " << ref << ", skolem = " << skolem << std::endl;
  d_nodeToSkolem[ref] = skolem;
  d_skolemToNode[skolem] = ref;
}

Node ProofSkolemization::getSkolem(Node ref) {
  Debug("gk::proof") << "ProofSkolemization: getSkolem( ";
  Assert (d_nodeToSkolem.find(ref) != d_nodeToSkolem.end());
  Debug("gk::proof") << ref << " ) = " << d_nodeToSkolem[ref] << std::endl;
  return d_nodeToSkolem[ref];
}

Node ProofSkolemization::getEquality(Node skolem) {
  Assert (d_skolemToNode.find(skolem) != d_skolemToNode.end());
  return d_skolemToNode[skolem];
}

bool ProofSkolemization::isSkolem(Node skolem) {
  return (d_skolemToNode.find(skolem) != d_skolemToNode.end());
}

void ProofSkolemization::clear() {
  Debug("gk::proof") << "ProofSkolemization: clear" << std::endl;
  d_nodeToSkolem.clear();
}

std::hash_map<Node, Node, NodeHashFunction>::const_iterator ProofSkolemization::begin() {
  return d_nodeToSkolem.begin();
}

std::hash_map<Node, Node, NodeHashFunction>::const_iterator ProofSkolemization::end() {
  return d_nodeToSkolem.end();
}

}/* CVC4::theory::arrays namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */
