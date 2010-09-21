/*********************                                                        */
/*! \file arith_constants.h
 ** \verbatim
 ** Original author: taking
 ** Major contributors: mdeters
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief [[ Add one-line brief description here ]]
 **
 ** [[ Add lengthier description here ]]
 ** \todo document this file
 **/

#include "cvc4_private.h"

#ifndef __CVC4__THEORY__ARITH__ARITH_CONSTANTS_H
#define __CVC4__THEORY__ARITH__ARITH_CONSTANTS_H

#include "expr/node.h"
#include "expr/node_manager.h"
#include "util/rational.h"
#include "theory/arith/delta_rational.h"

namespace CVC4 {
namespace theory {
namespace arith {

class ArithConstants{
public:
  Rational d_ZERO;
  Rational d_ONE;
  Rational d_NEGATIVE_ONE;

  DeltaRational d_ZERO_DELTA;

  Node d_ZERO_NODE;
  Node d_ONE_NODE;
  Node d_NEGATIVE_ONE_NODE;

  ArithConstants(NodeManager* nm) :
    d_ZERO(0,1),
    d_ONE(1,1),
    d_NEGATIVE_ONE(-1,1),
    d_ZERO_DELTA(d_ZERO),
    d_ZERO_NODE(nm->mkConst(d_ZERO)),
    d_ONE_NODE(nm->mkConst(d_ONE)),
    d_NEGATIVE_ONE_NODE(nm->mkConst(d_NEGATIVE_ONE))
  {}
};

}; /* namesapce arith */
}; /* namespace theory */
}; /* namespace CVC4 */

#endif /* __CVC4__THEORY__ARITH_ARITH_CONSTANTS_H */
