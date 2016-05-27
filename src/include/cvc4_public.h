/*********************                                                        */
/*! \file cvc4_public.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Morgan Deters, Tim King
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2016 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
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
#  define CVC4_PUBLIC
#else /* !( defined _WIN32 || defined __CYGWIN__ ) */
#  if __GNUC__ >= 4
#    define CVC4_PUBLIC __attribute__ ((__visibility__("default")))
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
#    define CVC4_UNDEFINED __attribute__((__error__("this function intentionally undefined")))
#  else /* GCC < 4.3.0 */
#    define CVC4_UNDEFINED
#  endif /* GCC >= 4.3.0 */
#else /* ! __GNUC__ */
#  define CVC4_UNDEFINED
#endif /* __GNUC__ */

#ifdef __GNUC__
#  define CVC4_UNUSED __attribute__((__unused__))
#  define CVC4_NORETURN __attribute__ ((__noreturn__))
#  define CVC4_CONST_FUNCTION __attribute__ ((__const__))
#  define CVC4_PURE_FUNCTION __attribute__ ((__pure__))
#  define CVC4_DEPRECATED __attribute__ ((__deprecated__))
#  define CVC4_WARN_UNUSED_RESULT __attribute__ ((__warn_unused_result__))
#else /* ! __GNUC__ */
#  define CVC4_UNUSED
#  define CVC4_NORETURN
#  define CVC4_CONST_FUNCTION
#  define CVC4_PURE_FUNCTION
#  define CVC4_DEPRECATED
#  define CVC4_WARN_UNUSED_RESULT
#endif /* __GNUC__ */

#endif /* __CVC4_PUBLIC_H */
