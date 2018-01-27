/*********************                                                        */
/*! \file fp_converter.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Martin Brain
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2017 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Conversion of floating-point operations to bit-vectors using symfpu.
 **/

#include "theory/fp/fp_converter.h"

#include <stack>

namespace CVC4 {
namespace theory {
namespace fp {

FpConverter::FpConverter(context::UserContext *user)
    : d_additionalAssertions(user) {}

Node FpConverter::convert(TNode node) {
  Unimplemented("Conversion not implemented.");
}

Node FpConverter::getValue(Valuation &val, TNode var) {
  Unimplemented("Conversion not implemented.");
}

}  // namespace fp
}  // namespace theory
}  // namespace CVC4
