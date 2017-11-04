/*********************                                                        */
/*! \file sygus_out_mode.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2017 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Options for sygus solution output.
 **/

#include "cvc4_public.h"

#ifndef __CVC4__SMT__SYGUS_OUT_MODE_H
#define __CVC4__SMT__SYGUS_OUT_MODE_H

#include <iosfwd>

namespace CVC4 {

/** Mode for printing sygus solutions. */
enum SygusSolutionOutMode
{
  /** print status */
  SYGUS_SOL_OUT_STATUS,
  /** (default) print status and solution */
  SYGUS_SOL_OUT_STATUS_AND_DEF,
  /** print status if infeasible, or solution if feasible */
  SYGUS_SOL_OUT_STATUS_OR_DEF,
  /** print output specified by sygus standard */
  SYGUS_SOL_OUT_STANDARD,
};

} /* CVC4 namespace */

#endif /* __CVC4__SMT__SYGUS_OUT_MODE_H */
