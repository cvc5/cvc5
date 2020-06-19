/*********************                                                        */
/*! \file nary_builder.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Tim King
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief [[ Add one-line brief description here ]]
 **
 ** [[ Add lengthier description here ]]
 ** \todo document this file
 **/


#include "cvc4_private.h"

#pragma once

#include <unordered_map>
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

  typedef std::unordered_map<Node, Node, NodeHashFunction> NodeMap;
  NodeMap d_cache;
};/* class RePairAssocCommutativeOperators */

}/* util namespace */
}/* CVC4 namespace */
