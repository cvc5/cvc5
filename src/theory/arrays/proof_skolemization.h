/*********************                                                        */
/*! \file proof_skolemization.h
 **/

#include "cvc4_private.h"

#ifndef __CVC4__THEORY__ARRAYS__PROOF_SKOLEMIZATION_H
#define __CVC4__THEORY__ARRAYS__PROOF_SKOLEMIZATION_H

#include "theory/theory.h"

namespace CVC4 {
namespace theory {
namespace arrays {

class ProofSkolemization {
public:
  static void registerSkolem(Node ref, Node skolem);
  static Node getSkolem(Node ref);
  static Node getEquality(Node skolem);
  static void clear();
  static bool isSkolem(Node skolem);

  static std::hash_map<Node, Node, NodeHashFunction>::const_iterator begin();
  static std::hash_map<Node, Node, NodeHashFunction>::const_iterator end();

private:
  static std::hash_map<Node, Node, NodeHashFunction> d_nodeToSkolem;
  static std::hash_map<Node, Node, NodeHashFunction> d_skolemToNode;
};/* class ProofSkolemization */

}/* CVC4::theory::arrays namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */

#endif /* __CVC4__THEORY__ARRAYS__PROOF_SKOLEMIZATION_H */
