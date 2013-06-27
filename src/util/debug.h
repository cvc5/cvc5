/*********************                                                        */
/*! \file debug.h
 ** \verbatim
 ** Original author: Morgan Deters
 ** Major contributors: none
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2013  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief Debugging things.
 **
 ** Debugging things.
 **
 ** These are low-level assertions!  Generally you should use
 ** CVC4::Assert() instead (they throw an exception!).  See
 ** util/Assert.h.
 **/

#include "cvc4_private.h"

#ifndef __CVC4__DEBUG_H
#define __CVC4__DEBUG_H

#include <cassert>

#ifdef CVC4_ASSERTIONS
// the __builtin_expect() helps us if assert is built-in or a macro
#  define cvc4assert(x) assert(__builtin_expect( ( x ), true ))
#else
// TODO: use a compiler annotation when assertions are off ?
// (to improve optimization)
#  define cvc4assert(x) /*__builtin_expect( ( x ), true )*/
#endif /* CVC4_ASSERTIONS */

#endif /* __CVC4__DEBUG_H */
