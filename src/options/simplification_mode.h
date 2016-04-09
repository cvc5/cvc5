/*********************                                                        */
/*! \file simplification_mode.h
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

#ifndef __CVC4__SMT__SIMPLIFICATION_MODE_H
#define __CVC4__SMT__SIMPLIFICATION_MODE_H

#include <iosfwd>

namespace CVC4 {

/** Enumeration of simplification modes (when to simplify). */
typedef enum {
  /** Simplify the assertions all together once a check is requested */
  SIMPLIFICATION_MODE_BATCH,
  /** Don't do simplification */
  SIMPLIFICATION_MODE_NONE
} SimplificationMode;

std::ostream& operator<<(std::ostream& out, SimplificationMode mode) CVC4_PUBLIC;

}/* CVC4 namespace */

#endif /* __CVC4__SMT__SIMPLIFICATION_MODE_H */
