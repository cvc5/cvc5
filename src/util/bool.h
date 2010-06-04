/*********************                                                        */
/*! \file bool.h
 ** \verbatim
 ** Original author: mdeters
 ** Major contributors: none
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief A multiprecision rational constant.
 **
 ** A multiprecision rational constant.
 ** This stores the rational as a pair of multiprecision integers,
 ** one for the numerator and one for the denominator.
 ** The number is always stored so that the gcd of the numerator and denominator
 ** is 1.  (This is referred to as referred to as canonical form in GMP's
 ** literature.) A consquence is that that the numerator and denominator may be
 ** different than the values used to construct the Rational.
 **/

#include "cvc4_public.h"

#ifndef __CVC4__BOOL_H
#define __CVC4__BOOL_H

namespace CVC4 {

struct BoolHashStrategy {
  static inline size_t hash(bool b) {
    return b;
  }
};/* struct BoolHashStrategy */

}/* CVC4 namespace */

#endif /* __CVC4__BOOL_H */
