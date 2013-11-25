
#include "cvc4_private.h"

#pragma once

#include <vector>
#include "expr/node.h"

namespace CVC4{
namespace util {

class NaryBuilder {
public:
  static Node mkAssoc(Kind k, const std::vector<Node>& children);
  static Node zeroArity(Kind k);
};/* class NaryBuilder */

class RePairAssocCommutativeOperators {
public:
  RePairAssocCommutativeOperators();
  ~RePairAssocCommutativeOperators();

  Node rePairAssocCommutativeOperators(TNode n);

  static bool isAssociateCommutative(Kind k);

  size_t size() const;
  void clear();
private:
  Node case_assoccomm(TNode n);
  Node case_other(TNode n);

  typedef std::hash_map<Node, Node, NodeHashFunction> NodeMap;
  NodeMap d_cache;
};/* class RePairAssocCommutativeOperators */

}/* util namespace */
}/* CVC4 namespace */
