/*********************                                                        */
/*! \file cvc4_public.h
 ** \verbatim
 ** Original author: mdeters
 ** Major contributors: none
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief Macros that should be defined everywhere during the building of
 ** the libraries and driver binary, and also exported to the user.
 **
 ** Macros that should be defined everywhere during the building of
 ** the libraries and driver binary, and also exported to the user.
 **/

#ifndef __CVC4_PUBLIC_H
#define __CVC4_PUBLIC_H

#include <stdint.h>

#if defined _WIN32 || defined __CYGWIN__
#  ifdef BUILDING_DLL
#    ifdef __GNUC__
#      define CVC4_PUBLIC __attribute__((dllexport))
#    else /* ! __GNUC__ */
#      define CVC4_PUBLIC __declspec(dllexport)
#    endif /* __GNUC__ */
#  else /* BUILDING_DLL */
#    ifdef __GNUC__
#      define CVC4_PUBLIC __attribute__((dllimport))
#    else /* ! __GNUC__ */
#      define CVC4_PUBLIC __declspec(dllimport)
#    endif /* __GNUC__ */
#  endif /* BUILDING_DLL */
#else /* !( defined _WIN32 || defined __CYGWIN__ ) */
#  if __GNUC__ >= 4
#    define CVC4_PUBLIC __attribute__ ((visibility("default")))
#  else /* !( __GNUC__ >= 4 ) */
#    define CVC4_PUBLIC
#  endif /* __GNUC__ >= 4 */
#endif /* defined _WIN32 || defined __CYGWIN__ */

// Can use CVC4_UNDEFINED for things like undefined, private
// copy constructors.  The advantage is that with CVC4_UNDEFINED,
// if something _does_ try to call the function, you get an error
// at the point of the call (rather than a link error later).

// CVC4_UNUSED is to mark something (e.g. local variable, function)
// as being _possibly_ unused, so that the compiler generates no
// warning about it.  This might be the case for e.g. a variable
// only used in DEBUG builds.

#ifdef __GNUC__
#  if __GNUC__ > 4 || ( __GNUC__ == 4 && __GNUC_MINOR__ >= 3 )
     /* error function attribute only exists in GCC >= 4.3.0 */
#    define CVC4_UNDEFINED __attribute__((error("this function intentionally undefined")))
#  else /* GCC < 4.3.0 */
#    define CVC4_UNDEFINED
#  endif /* GCC >= 4.3.0 */
#else /* ! __GNUC__ */
#  define CVC4_UNDEFINED
#endif /* __GNUC__ */

#ifdef __GNUC__
#  define CVC4_UNUSED __attribute__((unused))
#else /* ! __GNUC__ */
#  define CVC4_UNUSED
#endif /* __GNUC__ */

#define EXPECT_TRUE(x) __builtin_expect( (x), true )
#define EXPECT_FALSE(x) __builtin_expect( (x), false )
#define CVC4_NORETURN __attribute__ ((noreturn))

#ifndef NULL
#  define NULL ((void*) 0)
#endif

#endif /* __CVC4_PUBLIC_H */
