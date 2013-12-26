/*********************                                                        */
/*! \file bool.h
 ** \verbatim
 ** Original author: Morgan Deters
 ** Major contributors: none
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2013  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief A hash function for Boolean
 **
 ** A hash function for Boolean.
 **/

#include "cvc4_public.h"

#ifndef __CVC4__BOOL_H
#define __CVC4__BOOL_H

namespace CVC4 {

struct BoolHashFunction {
  inline size_t operator()(bool b) const {
    return b;
  }
};/* struct BoolHashFunction */

}/* CVC4 namespace */

#endif /* __CVC4__BOOL_H */
