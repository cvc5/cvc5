/*********************                                                        */
/*! \file smt_modes.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Morgan Deters, Dejan Jovanovic
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
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

#ifndef __CVC4__SMT__MODES_H
#define __CVC4__SMT__MODES_H

#include <iosfwd>

namespace CVC4 {

/** Enumeration of simplification modes (when to simplify). */
enum SimplificationMode
{
  /** Simplify the assertions all together once a check is requested */
  SIMPLIFICATION_MODE_BATCH,
  /** Don't do simplification */
  SIMPLIFICATION_MODE_NONE
};

std::ostream& operator<<(std::ostream& out,
                         SimplificationMode mode) CVC4_PUBLIC;

/** Enumeration of model core modes. */
enum ModelCoresMode
{
  /** Do not compute model cores */
  MODEL_CORES_NONE,
  /**
   * Compute "simple" model cores that exclude variables that do not
   * contribute to satisfying the input.
   */
  MODEL_CORES_SIMPLE,
  /**
   * Compute model cores that also exclude variables whose variables are implied
   * by others.
   */
  MODEL_CORES_NON_IMPLIED
};

}  // namespace CVC4

#endif /* __CVC4__SMT__MODES_H */
