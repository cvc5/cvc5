/*********************                                                        */
/*! \file arithvar.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Tim King
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Defines ArithVar which is the internal representation of variables in arithmetic
 **
 ** This defines ArithVar which is the internal representation of variables in
 ** arithmetic. This is a typedef from Index to ArithVar.
 ** This file also provides utilities for ArithVars.
 **/


#include "cvc4_private.h"

#pragma once

#include <vector>

#include "util/index.h"
#include "util/rational.h"

namespace CVC4 {
namespace theory {
namespace arith {

typedef Index ArithVar;
extern const ArithVar ARITHVAR_SENTINEL;

typedef std::vector<ArithVar> ArithVarVec;
typedef std::pair<ArithVar, Rational> ArithRatPair;
typedef std::vector< ArithRatPair > ArithRatPairVec;

extern bool debugIsASet(const ArithVarVec& variables);


}/* CVC4::theory::arith namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */
