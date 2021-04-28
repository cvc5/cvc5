/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Tim King, Mathias Preiner
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Typing and cardinality rules for the theory of sep.
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__SEP__THEORY_SEP_TYPE_RULES_H
#define CVC5__THEORY__SEP__THEORY_SEP_TYPE_RULES_H

#include "expr/node.h"
#include "expr/type_node.h"

namespace cvc5 {
namespace theory {
namespace sep {

class SepEmpTypeRule
{
 public:
  static TypeNode computeType(NodeManager* nodeManager, TNode n, bool check);
};

struct SepPtoTypeRule
{
  static TypeNode computeType(NodeManager* nodeManager, TNode n, bool check);
};

struct SepStarTypeRule
{
  static TypeNode computeType(NodeManager* nodeManager, TNode n, bool check);
};

struct SepWandTypeRule
{
  static TypeNode computeType(NodeManager* nodeManager, TNode n, bool check);
};

struct SepLabelTypeRule
{
  static TypeNode computeType(NodeManager* nodeManager, TNode n, bool check);
};

struct SepNilTypeRule
{
  static TypeNode computeType(NodeManager* nodeManager, TNode n, bool check);
};

}  // namespace sep
}  // namespace theory
}  // namespace cvc5

#endif /* CVC5__THEORY__SEP__THEORY_SEP_TYPE_RULES_H */
