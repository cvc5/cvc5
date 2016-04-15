/*********************                                                        */
/*! \file skolemization_manager.h
 **/

#include "cvc4_private.h"

#ifndef __CVC4__SKOLEMIZATION_MANAGER_H
#define __CVC4__SKOLEMIZATION_MANAGER_H

#include <iostream>
#include <map>
#include "proof/proof.h"
#include "util/proof.h"
#include "expr/node.h"
#include "theory/logic_info.h"
#include "theory/substitutions.h"

namespace CVC4 {

class SkolemizationManager {
public:
  void registerSkolem(Node disequality, Node skolem);
  bool hasSkolem(Node disequality);
  Node getSkolem(Node disequality);
  Node getDisequality(Node skolem);
  bool isSkolem(Node skolem);
  // void registerLemmaForSkolem(Node skolem, Node lemma);
  // Node getLemma(Node skolem);

  void clear();

  std::hash_map<Node, Node, NodeHashFunction>::const_iterator begin();
  std::hash_map<Node, Node, NodeHashFunction>::const_iterator end();

private:
  std::hash_map<Node, Node, NodeHashFunction> d_disequalityToSkolem;
  std::hash_map<Node, Node, NodeHashFunction> d_skolemToDisequality;
  std::hash_map<Node, Node, NodeHashFunction> d_skolemToLemma;
};

}/* CVC4 namespace */



#endif /* __CVC4__SKOLEMIZATION_MANAGER_H */
