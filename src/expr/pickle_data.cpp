/*********************                                                        */
/*! \file pickle_data.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Morgan Deters, Tim King
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2016 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief This is a "pickle" for expressions, CVC4-internal view
 **
 ** This is the CVC4-internal view (private data structure) for a
 ** "pickle" for expressions.  The public-facing view is a "Pickle",
 ** which just points to a PickleData.  A pickle is a binary
 ** serialization of an expression that can be converted back into an
 ** expression in the same or another ExprManager.
 **/

#include <iostream>
#include <sstream>
#include <string>

#include "base/cvc4_assert.h"
#include "expr/pickle_data.h"
#include "expr/expr.h"
#include "expr/node.h"
#include "expr/node_manager.h"
#include "expr/node_value.h"
#include "expr/expr_manager_scope.h"
#include "expr/variable_type_map.h"
#include "expr/kind.h"
#include "expr/metakind.h"

namespace CVC4 {
namespace expr {
namespace pickle {

void PickleData::writeToStringStream(std::ostringstream& oss) const {
  BlockDeque::const_iterator i = d_blocks.begin(), end = d_blocks.end();
  for(; i != end; ++i) {
    Block b = *i;
    Assert(sizeof(b) * 8 == NBITS_BLOCK);
    oss << b.d_body.d_data << " ";
  }
}

std::string PickleData::toString() const {
  std::ostringstream oss;
  oss.flags(std::ios::oct | std::ios::showbase);
  writeToStringStream(oss);
  return oss.str();
}

}/* CVC4::expr::pickle namespace */
}/* CVC4::expr namespace */
}/* CVC4 namespace */
