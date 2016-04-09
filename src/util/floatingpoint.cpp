/*********************                                                        */
/*! \file floatingpoint.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Tim King, Martin Brain
 ** Copyright (c) 2013  University of Oxford
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2016 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief [[ Implementations of the utility functions for working with floating point theories. ]]
 **
 **/

#include "util/floatingpoint.h"

#include "base/cvc4_assert.h"

namespace CVC4 {

FloatingPointSize::FloatingPointSize (unsigned _e, unsigned _s) : e(_e), s(_s)
{
  PrettyCheckArgument(validExponentSize(_e),_e,"Invalid exponent size : %d",_e);
  PrettyCheckArgument(validSignificandSize(_s),_s,"Invalid significand size : %d",_s);
}

FloatingPointSize::FloatingPointSize (const FloatingPointSize &old) : e(old.e), s(old.s)
{
  PrettyCheckArgument(validExponentSize(e),e,"Invalid exponent size : %d",e);
  PrettyCheckArgument(validSignificandSize(s),s,"Invalid significand size : %d",s);
}

void FloatingPointLiteral::unfinished (void) const {
  Unimplemented("Floating-point literals not yet implemented.");
}

}/* CVC4 namespace */
