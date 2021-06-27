/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Rewrite database
 */

#include "theory/rewrite_term_util.h"

using namespace cvc5::kind;

namespace cvc5 {
namespace theory {

struct IsListTag
{
};
using IsListAttr = expr::Attribute<IsListTag, bool>;

void markRewriteListVar(TNode fv)
{
  Assert(fv.getKind() == BOUND_VARIABLE);
  fv.setAttribute(IsListAttr(), true);
}

bool isRewriteListVar(TNode fv)
{
  return fv.hasAttribute(isListAttr());
}

}  // namespace theory
}  // namespace cvc5
