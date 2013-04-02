/*********************                                                        */
/*! \file bool.h
 ** \verbatim
 ** Original author: Morgan Deters
 ** Major contributors: none
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2013  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief A multi-precision rational constant.
 **
 ** A multi-precision rational constant.
 ** This stores the rational as a pair of multi-precision integers,
 ** one for the numerator and one for the denominator.
 ** The number is always stored so that the gcd of the numerator and denominator
 ** is 1.  (This is referred to as referred to as canonical form in GMP's
 ** literature.) A consequence is that that the numerator and denominator may be
 ** different than the values used to construct the Rational.
 **/

#include "cvc4_public.h"

#ifndef __CVC4__BOOL_H
#define __CVC4__BOOL_H

namespace CVC4 {

struct BoolHashFunction {
  inline size_t operator()(bool b) const {
    return b;
  }
};/* struct BoolHashFunction */

}/* CVC4 namespace */

#endif /* __CVC4__BOOL_H */
