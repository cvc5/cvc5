/*********************                                                        */
/*! \file theory.h
 ** \verbatim
 ** Original author: mdeters
 ** Major contributors: dejan
 ** Minor contributors (to current version): taking, barrett
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010, 2011  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief Base of the theory interface.
 **
 ** Base of the theory interface.
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
};

}
}

