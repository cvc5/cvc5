/*********************                                                        */
/*! \file index.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Mathias Preiner, Tim King
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Standardized type for efficient array indexing.
 **
 ** Standardized type for efficient array indexing.
 **/

#include "cvc4_private.h"

#ifndef CVC4__INDEX_H
#define CVC4__INDEX_H

namespace cvc5 {

/** Index is a standardized unsigned integer used for efficient indexing. */
using Index = uint32_t;

}  // namespace cvc5

#endif /* CVC4__INDEX_H */
