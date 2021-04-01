/*********************                                                        */
/*! \file bool.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Morgan Deters, Mathias Preiner
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief A hash function for Boolean
 **
 ** A hash function for Boolean.
 **/

#include "cvc4_public.h"

#ifndef CVC4__BOOL_H
#define CVC4__BOOL_H

namespace cvc5 {

struct BoolHashFunction {
  inline size_t operator()(bool b) const {
    return b;
  }
};/* struct BoolHashFunction */

}  // namespace cvc5

#endif /* CVC4__BOOL_H */
