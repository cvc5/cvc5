/*********************                                                        */
/*! \file arith_propagation_mode.h
 ** \verbatim
 ** Original author: Morgan Deters
 ** Major contributors: none
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2013  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief [[ Add one-line brief description here ]]
 **
 ** [[ Add lengthier description here ]]
 ** \todo document this file
 **/

#include "cvc4_public.h"

#ifndef __CVC4__THEORY__ARITH__ARITH_PROPAGATION_MODE_H
#define __CVC4__THEORY__ARITH__ARITH_PROPAGATION_MODE_H

#include <iostream>

namespace CVC4 {

typedef enum {
  NO_PROP,
  UNATE_PROP,
  BOUND_INFERENCE_PROP,
  BOTH_PROP
} ArithPropagationMode;

std::ostream& operator<<(std::ostream& out, ArithPropagationMode rule) CVC4_PUBLIC;

}/* CVC4 namespace */

#endif /* __CVC4__THEORY__ARITH__ARITH_PROPAGATION_MODE_H */
