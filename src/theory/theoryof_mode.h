/*********************                                                        */
/*! \file theoryof_mode.h
 ** \verbatim
 ** Original author: Dejan Jovanovic
 ** Major contributors: Morgan Deters
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2013  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief Option selection for theoryOf() operation
 **
 ** Option selection for theoryOf() operation.
 **/

#pragma once

#include "cvc4_public.h"

namespace CVC4 {
namespace theory {

/** How do we associate theories with the terms */
enum TheoryOfMode {
  /** Equality, variables and constants are associated with the types */
  THEORY_OF_TYPE_BASED,
  /** Variables are uninterpreted, constants are with the type, equalities prefer parametric */
  THEORY_OF_TERM_BASED
};/* enum TheoryOfMode */

}/* CVC4::theory namespace */
}/* CVC4 namespace */

