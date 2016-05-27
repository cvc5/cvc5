/*********************                                                        */
/*! \file arith_heuristic_pivot_rule.h
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

#ifndef __CVC4__THEORY__ARITH__ARITH_HEURISTIC_PIVOT_RULE_H
#define __CVC4__THEORY__ARITH__ARITH_HEURISTIC_PIVOT_RULE_H

#include <iostream>

namespace CVC4 {

enum ErrorSelectionRule {
  VAR_ORDER,
  MINIMUM_AMOUNT,
  MAXIMUM_AMOUNT,
  SUM_METRIC
};

std::ostream& operator<<(std::ostream& out, ErrorSelectionRule rule) CVC4_PUBLIC;

}/* CVC4 namespace */

#endif /* __CVC4__THEORY__ARITH__ARITH_HEURISTIC_PIVOT_RULE_H */
