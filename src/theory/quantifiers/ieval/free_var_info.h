/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Info per free variable in instantiation evaluator.
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__QUANTIFIERS__IEVAL__FREE_VAR_INFO_H
#define CVC5__THEORY__QUANTIFIERS__IEVAL__FREE_VAR_INFO_H

#include <unordered_set>

#include "context/cdlist.h"
#include "expr/node.h"

namespace cvc5::internal {
namespace theory {
namespace quantifiers {
namespace ieval {

/** Information for a free variable. */
class FreeVarInfo
{
  using NodeList = context::CDList<Node>;

 public:
  FreeVarInfo(context::Context* c);
  /** List of quantifiers that contain this variable */
  NodeList d_quantList;
};

}  // namespace ieval
}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal

#endif
