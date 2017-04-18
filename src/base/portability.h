/*********************                                                        */
/*! \file portability.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Caleb Donovick
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2016 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Transparent macros for compiler specific and c++11 features.
 **
 ** Transparent macros for compiler specific and c++11 features.
 **/

#ifndef __CVC4__PORTABILITY_H
#define __CVC4__PORTABILITY_H

/* Portable macros */
#ifdef __CVC4__expect
  #error "__CVC4__expect was defined outside of " __FILE__ ", something is going to break"
#endif /* __CVC4__expect */

#if defined __GUNC__
  /* !cond !expect ensure currect types are passed to __builtin_expect */
  #define __CVC4__expect(cond, expect)  __builtin_expect((!(cond)),(!(expect)))
#else
  #define __CVC4__expect(cond, expect) (cond)
#endif


#ifdef __CVC4__FUNC_STRING
  #error "__CVC4__FUNC_STRING was defined outside of " __FILE__ ", something is going to break"
#endif /* __CVC4__FUNC_STRING */

#if defined __GNUC__
  #define __CVC4__FUNC_STRING __PRETTY_FUNCTION__
#elif  __cplusplus >= 201103L
  #define __CVC4__FUNC_STRING __func__
#elif defined __FUNCTION__
  #define __CVC4__FUNC_STRING __FUNCTION__
#else
  // No way to determine the name of the function
  #define __CVC4__FUNC_STRING ""
#endif


#ifdef __CVC4__noreturn
  #error "__CVC4__NO_RETURN was defined outside of " __FILE__ ", something is going to break"
#endif /* __CVC4__NO_RETURN */

#if __cplusplus >= 201103L
  #define __CVC4__noreturn [[noreturn]]
#elif defined __GNUC__
  #define __CVC4__noreturn __attribute__((noreturn))
#else
  #define __CVC4__noreturn
#endif


#endif /* __CVC4__PORTABILITY_H */

