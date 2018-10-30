/*********************                                                        */
/*! \file decision_stoponly.h
** \verbatim
** Top contributors (to current version):
**   Haoze Wu
** This file is part of the CVC4 project.
** Copyright (c) 2009-2018 by the authors listed in the file AUTHORS
** in the top-level source directory) and their institutional affiliations.
** All rights reserved.  See the file COPYING in the top-level source
** directory for licensing information.\endverbatim
**
** \brief Rewriter attributes
**
** Rewriter attributes.
**/

#include "cvc4_private.h"

#ifndef __CVC4__OPTIONS__DECISION_STOPONLY_H
#define __CVC4__OPTIONS__DECISION_STOPONLY_H

namespace CVC4 {
namespace decision {

enum StopOnly
{
  Off,    // not using stoponly
  VSIDS,  // use vsids + justification stoponly
  LRB     // use learning-rate-based heuristics + justification stoponly
};

}  // namespace decision
}  // namespace CVC4

#endif /* __CVC4__OPTIONS__DECISION_STOPONLY_H */
