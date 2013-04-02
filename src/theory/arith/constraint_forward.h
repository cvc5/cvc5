/*********************                                                        */
/*! \file constraint_forward.h
 ** \verbatim
 ** Original author: Tim King
 ** Major contributors: none
 ** Minor contributors (to current version): Morgan Deters
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2013  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief Forward declarations of the ConstraintValue and ConstraintDatabase classes.
 **
 ** This is the forward declarations of the ConstraintValue and ConstraintDatabase
 ** and the typedef for Constraint.  This is used to break circular dependencies and
 ** minimize interaction between header files.
 **/

#include "cvc4_private.h"

#ifndef __CVC4__THEORY__ARITH__CONSTRAINT_FORWARD_H
#define __CVC4__THEORY__ARITH__CONSTRAINT_FORWARD_H

namespace CVC4 {
namespace theory {
namespace arith {

class ConstraintValue;
typedef ConstraintValue* Constraint;
typedef const ConstraintValue* const ConstConstraint;

static const Constraint NullConstraint = NULL;

class ConstraintDatabase;

}/* CVC4::theory::arith namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */

#endif /* __CVC4__THEORY__ARITH__CONSTRAINT_FORWARD_H */
