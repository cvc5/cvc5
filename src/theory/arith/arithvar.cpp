/*********************                                                        */
/*! \file arithvar.cpp
 ** \verbatim
 ** Original author: Tim King
 ** Major contributors: Morgan Deters
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2013  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief [[ Add one-line brief description here ]]
 **
 ** [[ Add lengthier description here ]]
 ** \todo document this file
 **/


#include "theory/arith/arithvar.h"
#include <limits>

namespace CVC4 {
namespace theory {
namespace arith {

const ArithVar ARITHVAR_SENTINEL = std::numeric_limits<ArithVar>::max();

}/* CVC4::theory::arith namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */
