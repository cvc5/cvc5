/*********************                                           -*- C++ -*-  */
/** cvc4_config.h
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009 The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.
 **
 ** [[ Add file-specific comments here ]]
 **/

#ifndef __CVC4_CONFIG_H
#define __CVC4_CONFIG_H

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

#define EXPECT_TRUE(x) __builtin_expect( (x), true)
#define EXPECT_FALSE(x) __builtin_expect( (x), false)
#define NORETURN __attribute__ ((noreturn))

#ifndef NULL
#  define NULL ((void*) 0)
#endif

#endif /* __CVC4_CONFIG_H */
