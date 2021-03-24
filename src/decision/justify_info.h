/*********************                                                        */
/*! \file justify_info.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Justification info
 **/

#include "cvc4_private.h"

#ifndef CVC4__DECISION__JUSTIFY_INFO_H
#define CVC4__DECISION__JUSTIFY_INFO_H

#include "context/cdo.h"
#include "expr/node.h"
#include "prop/sat_solver_types.h"

namespace CVC4 {

/**
 * Information concerning a single formula in the justification strategy.
 */
class JustifyInfo
{
 public:
  JustifyInfo(context::Context* c)
      : d_node(c), d_desiredVal(c, prop::SAT_VALUE_UNKNOWN), d_childIndex(c, 0)
  {
  }
  /** The node we are considering */
  context::CDO<Node> d_node;
  /** Desired value */
  context::CDO<prop::SatValue> d_desiredVal;
  /** The child index we are considering */
  context::CDO<size_t> d_childIndex;
};

}  // namespace CVC4

#endif /* CVC4__DECISION__JUSTIFY_INFO_H */
