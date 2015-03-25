/*********************                                                        */
/*! \file floatingpoint.cpp
 ** \verbatim
 ** Original author: Martin Brain
 ** Major contributors:
 ** Minor contributors (to current version):
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2013  University of Oxford
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief [[ Implementations of the utility functions for working with floating point theories. ]]
 **
 **/

#include "util/cvc4_assert.h"
#include "util/floatingpoint.h"

namespace CVC4 {

  FloatingPointSize::FloatingPointSize (unsigned _e, unsigned _s) : e(_e), s(_s)
  {
    CheckArgument(validExponentSize(_e),_e,"Invalid exponent size : %d",_e);
    CheckArgument(validSignificandSize(_s),_s,"Invalid significand size : %d",_s);
  }

  FloatingPointSize::FloatingPointSize (const FloatingPointSize &old) : e(old.e), s(old.s)
  {
    CheckArgument(validExponentSize(e),e,"Invalid exponent size : %d",e);
    CheckArgument(validSignificandSize(s),s,"Invalid significand size : %d",s);
  }

  void FloatingPointLiteral::unfinished (void) const {
    Unimplemented("Floating-point literals not yet implemented.");
  }

}/* CVC4 namespace */

