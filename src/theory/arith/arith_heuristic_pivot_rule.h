/*********************                                                        */
/*! \file arith_heuristic_pivot_rule.h
 ** \verbatim
 ** Original author: mdeters
 ** Major contributors: none
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009-2012  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
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

typedef enum {
  MINIMUM,
  BREAK_TIES,
  MAXIMUM
} ArithHeuristicPivotRule;

std::ostream& operator<<(std::ostream& out, ArithHeuristicPivotRule rule) CVC4_PUBLIC;

}/* CVC4 namespace */

#endif /* __CVC4__THEORY__ARITH__ARITH_HEURISTIC_PIVOT_RULE_H */
