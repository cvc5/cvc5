/*********************                                                        */
/*! \file fun_def_evaluator.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Techniques for evaluating recursively defined functions
 **/

#include "cvc4_private.h"

#ifndef CVC4__QUANTIFIERS_FUN_DEF_EVALUATOR_H
#define CVC4__QUANTIFIERS_FUN_DEF_EVALUATOR_H

#include <map>
#include <vector>
#include "expr/attribute.h"
#include "expr/node.h"
#include "expr/type_node.h"

namespace CVC4 {
namespace theory {
namespace quantifiers {

/**
 * Techniques for evaluating recursively defined functions.
 */
class FunDefEvaluator
{
 public:
  FunDefEvaluator();
  ~FunDefEvaluator() {}
  /** assert definition */
  void assertDefinition(Node q);
  /** simplify node */
  Node simplifyNode(Node n);

 private:
  /** information cached per function definition */
  class FunDefInfo
  {
   public:
    /** the body */
    Node d_body;
    /** the formal argument list */
    std::vector<Node> d_args;
  };
  /** maps functions to their body and argument list */
  std::map<Node, FunDefInfo> d_funDefMap;
};

}  // namespace quantifiers
}  // namespace theory
}  // namespace CVC4

#endif
