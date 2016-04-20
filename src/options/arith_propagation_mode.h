/*********************                                                        */
/*! \file arith_propagation_mode.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Morgan Deters, Tim King
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2016 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
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

enum ArithPropagationMode {
  NO_PROP,
  UNATE_PROP,
  BOUND_INFERENCE_PROP,
  BOTH_PROP
};

std::ostream& operator<<(std::ostream& out, ArithPropagationMode rule) CVC4_PUBLIC;

}/* CVC4 namespace */

#endif /* __CVC4__THEORY__ARITH__ARITH_PROPAGATION_MODE_H */
