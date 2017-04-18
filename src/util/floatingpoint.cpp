/*********************                                                        */
/*! \file floatingpoint.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Martin Brain, Tim King, Paul Meng
 ** Copyright (c) 2013  University of Oxford
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2017 by the authors listed in the file AUTHORS
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
  PrettyCheckArgument(validExponentSize(_e),_e) << "Invalid exponent size : " << _e << std::endl;
  PrettyCheckArgument(validSignificandSize(_s),_s) << "Invalid significand size : " << _s << std::endl;
}

FloatingPointSize::FloatingPointSize (const FloatingPointSize &old) : e(old.e), s(old.s)
{
  PrettyCheckArgument(validExponentSize(e),e) << "Invalid exponent size : " << e << std::endl;
  PrettyCheckArgument(validSignificandSize(s),s) << "Invalid significand size : " << s << std::endl;
}

void FloatingPointLiteral::unfinished (void) const {
  Unimplemented() << "Floating-point literals not yet implemented." << std::endl;
}

}/* CVC4 namespace */
