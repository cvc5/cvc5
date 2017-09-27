/*********************                                                        */
/*! \file fp_converter.cpp
 ** \verbatim
 ** Original author: Martin Brain
 ** Major contributors:
 ** Minor contributors (to current version):
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2014  University of Oxford
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief [[ Conversion of floating-point operations to bit-vectors using
 ** symfpu. ]]
 **
 **/

#include <stack>

#include "theory/fp/fp_converter.h"

namespace CVC4 {
namespace theory {
namespace fp {

fpConverter::FpConverter(context::UserContext *user)
    : d_additionalAssertions(user) {}

Node FpConverter::convert(TNode node) {
  Unimplemented("Conversion not implemented.");
  return node;
}

Node FpConverter::getValue(Valuation &val, TNode var) {
  Unimplemented("Conversion not implemented.");
  return Node::null();
}

}  // namespace fp
}  // namespace theory
}  // namespace CVC4
