/*********************                                                        */
/*! \file bool_to_bv_mode.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Makai Mann
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** [[ Add lengthier description here ]]

 ** \todo document this file

**/

#include "cvc4_private.h"

#ifndef __CVC4__PREPROCESSING__PASSES__BOOL_TO_BV_MODE_H
#define __CVC4__PREPROCESSING__PASSES__BOOL_TO_BV_MODE_H

#include <iosfwd>

namespace CVC4 {
namespace preprocessing {
namespace passes {

/** Enumeration of bool-to-bv modes */
enum BoolToBVMode
{
  /**
   * No bool-to-bv pass
   */
  BOOL_TO_BV_OFF,

  /**
   * Only lower bools in condition of ITEs
   * Tries to give more info to bit-vector solver
   * by using bit-vector-ITEs when possible
   */
  BOOL_TO_BV_ITE,

  /**
   * Lower every bool beneath the top layer to be a
   * bit-vector
   */
  BOOL_TO_BV_ALL
};
}
}

std::ostream& operator<<(std::ostream& out, preprocessing::passes::BoolToBVMode mode);

}

#endif /* __CVC4__PREPROCESSING__PASSES__BOOL_TO_BV_MODE_H */
