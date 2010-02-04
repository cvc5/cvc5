/*********************                                                        */
/** debug.h
 ** Original author: mdeters
 ** Major contributors: none
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.
 **
 ** Debugging things.
 **
 ** These are low-level assertions!  Generally you should use
 ** CVC4::Assert() instead (they throw an exception!).  See
 ** util/Assert.h.
 **/

#ifndef __CVC4__DEBUG_H
#define __CVC4__DEBUG_H

#include "cvc4_config.h"

#include <cassert>

#ifdef CVC4_ASSERTIONS
// the __builtin_expect() helps us if assert is built-in or a macro
#  define cvc4assert(x) assert(EXPECT_TRUE( x ))
#else
// TODO: use a compiler annotation when assertions are off ?
// (to improve optimization)
#  define cvc4assert(x) /*EXPECT_TRUE( x )*/
#endif /* CVC4_ASSERTIONS */

#endif /* __CVC4__DEBUG_H */
