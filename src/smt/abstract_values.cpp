/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Morgan Deters
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Utility for constructing and maintaining abstract values.
 */

#include "smt/abstract_values.h"

#include "expr/ascription_type.h"
#include "expr/skolem_manager.h"
#include "options/smt_options.h"

namespace cvc5 {
namespace smt {

AbstractValues::AbstractValues(NodeManager* nm)
    : d_nm(nm),
      d_fakeContext(),
      d_abstractValueMap(&d_fakeContext),
      d_abstractValues()
{
}
AbstractValues::~AbstractValues() {}

Node AbstractValues::substituteAbstractValues(TNode n)
{
  // We need to do this even if options::abstractValues() is off,
  // since the setting might have changed after we already gave out
  // some abstract values.
  return d_abstractValueMap.apply(n);
}

Node AbstractValues::mkAbstractValue(TNode n)
{
  Assert(options::abstractValues());
  Node& val = d_abstractValues[n];
  if (val.isNull())
  {
    val = d_nm->getSkolemManager()->mkDummySkolem(
        "a",
        n.getType(),
        "an abstract value",
        SkolemManager::SKOLEM_ABSTRACT_VALUE);
    d_abstractValueMap.addSubstitution(val, n);
  }
  return val;
}

}  // namespace smt
}  // namespace cvc5
