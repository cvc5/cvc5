/*********************                                                        */
/*! \file theoryof_mode.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Dejan Jovanovic, Morgan Deters, Tim King
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2016 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Option selection for theoryOf() operation
 **
 ** Option selection for theoryOf() operation.
 **/

#include "cvc4_public.h"

#pragma once

#include <ostream>

namespace CVC4 {
namespace theory {

/** How do we associate theories with the terms */
enum TheoryOfMode {
  /** Equality, variables and constants are associated with the types */
  THEORY_OF_TYPE_BASED,
  /** Variables are uninterpreted, constants are with the type, equalities prefer parametric */
  THEORY_OF_TERM_BASED
};/* enum TheoryOfMode */

std::ostream& operator<<(std::ostream& out, TheoryOfMode m) throw() CVC4_PUBLIC;

}/* CVC4::theory namespace */
}/* CVC4 namespace */

