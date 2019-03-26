/*********************                                                        */
/*! \file datatypes_modes.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
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

#ifndef __CVC4__BASE__DATATYPES_MODES_H
#define __CVC4__BASE__DATATYPES_MODES_H

#include <iostream>

namespace CVC4 {
namespace theory {

enum SygusFairMode {
  /** enforce fairness by direct conflict lemmas */
  SYGUS_FAIR_DIRECT,
  /** enforce fairness by datatypes size */
  SYGUS_FAIR_DT_SIZE,
  /** enforce fairness by datatypes height bound */
  SYGUS_FAIR_DT_HEIGHT_PRED,
  /** enforce fairness by datatypes size bound */
  SYGUS_FAIR_DT_SIZE_PRED,
  /** do not use fair strategy for CEGQI */
  SYGUS_FAIR_NONE,
};

}/* CVC4::theory namespace */
}/* CVC4 namespace */

#endif /* __CVC4__BASE__DATATYPES_MODES_H */
