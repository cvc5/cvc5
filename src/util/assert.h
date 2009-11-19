/*********************                                           -*- C++ -*-  */
/** assert.h
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009 The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.
 **
 **/

#ifndef __CVC4__ASSERT_H
#define __CVC4__ASSERT_H

#include <cassert>

#ifdef DEBUG
// the __builtin_expect() helps us if assert is built-in or a macro
# define cvc4assert(x) assert(__builtin_expect((x), 1))
#else
// TODO: use a compiler annotation when assertions are off ?
// (to improve optimization)
# define cvc4assert(x)
#endif /* DEBUG */

#endif /* __CVC4__ASSERT_H */
