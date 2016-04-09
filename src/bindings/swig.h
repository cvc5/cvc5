/*********************                                                        */
/*! \file swig.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Morgan Deters, Tim King
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2016 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Common swig checks and definitions
 **
 ** Common swig checks and definitions, when generating swig interfaces.
 **/

#ifndef __CVC4__BINDINGS__SWIG_H
#define __CVC4__BINDINGS__SWIG_H

#ifndef SWIG
#  error This file should only be included when generating swig interfaces.
#endif /* SWIG */

#if !defined(SWIG_VERSION) || SWIG_VERSION < 0x020000
#  error CVC4 bindings require swig version 2.0.0 or later, sorry.
#endif /* SWIG_VERSION */

%import "cvc4_public.h"
#warning "Working around a SWIG segfault in C++ template parsing."
//%import "base/tls.h"
#define CVC4_THREADLOCAL(__type...) __type
#define CVC4_THREADLOCAL_PUBLIC(__type...) CVC4_PUBLIC __type
#define CVC4_THREADLOCAL_TYPE(__type...) __type

// swig doesn't like the __thread storage class...
#define __thread
// ...or GCC attributes
#define __attribute__(x)

#endif /* __CVC4__BINDINGS__SWIG_H */
