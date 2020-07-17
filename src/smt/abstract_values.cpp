/*********************                                                        */
/*! \file abstract_values.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Utility for constructing and maintaining abstract values.
 **/

#include "smt/abstract_values.h"

#include "options/smt_options.h"

namespace CVC4 {
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
    val = d_nm->mkAbstractValue(n.getType());
    d_abstractValueMap.addSubstitution(val, n);
  }
  // We are supposed to ascribe types to all abstract values that go out.
  Node ascription = d_nm->mkConst(AscriptionType(n.getType().toType()));
  Node retval = d_nm->mkNode(kind::APPLY_TYPE_ASCRIPTION, ascription, val);
  return retval;
}

}  // namespace smt
}  // namespace CVC4
