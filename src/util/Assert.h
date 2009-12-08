/*********************                                           -*- C++ -*-  */
/** assert.h
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009 The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.
 **
 ** Assertion utility classes, functions, and exceptions.
 **/

#ifndef __CVC4__ASSERT_H
#define __CVC4__ASSERT_H

#include <string>
#include "util/exception.h"
#include "cvc4_config.h"
#include "config.h"

namespace CVC4 {

class CVC4_PUBLIC AssertionException : public Exception {
public:
  AssertionException() : Exception() {}
  AssertionException(std::string msg) : Exception(msg) {}
  AssertionException(const char* msg) : Exception(msg) {}
};/* class AssertionException */

class CVC4_PUBLIC UnreachableCodeException : public AssertionException {
public:
  UnreachableCodeException() : AssertionException() {}
  UnreachableCodeException(std::string msg) : AssertionException(msg) {}
  UnreachableCodeException(const char* msg) : AssertionException(msg) {}
};/* class UnreachableCodeException */

class CVC4_PUBLIC UnhandledCaseException : public UnreachableCodeException {
public:
  UnhandledCaseException() : UnreachableCodeException() {}
  UnhandledCaseException(std::string msg) : UnreachableCodeException(msg) {}
  UnhandledCaseException(const char* msg) : UnreachableCodeException(msg) {}
};/* class UnhandledCaseException */

#ifdef CVC4_ASSERTIONS
#  define Assert(cond, msg...) __CVC4_ASSERTGLUE("Assertion failure at " __FILE__ ":", __LINE__, ":  " #cond, __builtin_expect((cond), 1), ## msg)
#else /* ! CVC4_ASSERTIONS */
#  define Assert(cond, msg...) /*EXPECT_TRUE( cond )*/
#endif /* CVC4_ASSERTIONS */

#define AlwaysAssert(cond, msg...) __CVC4_ASSERTGLUE("Assertion failure at " __FILE__ ":", __LINE__, ":  " #cond, __builtin_expect((cond), 1), ## msg)
#define Unreachable(msg...) __CVC4_UNREACHABLEGLUE("Hit a section of unreachable code at " __FILE__ ":", __LINE__, ## msg)
#define Unhandled(msg...) __CVC4_UNHANDLEDGLUE("Hit an unhandled case at " __FILE__ ":", __LINE__, ## msg)

#define __CVC4_ASSERTGLUE(str1, line, str2, cond, msg...) AssertImpl(str1 #line str2, cond, ## msg)
#define __CVC4_UNREACHABLEGLUE(str, line, msg...) UnreachableImpl(str #line, ## msg)
#define __CVC4_UNHANDLEDGLUE(str, line, msg...) UnhandledImpl(str #line, ## msg)

inline void AssertImpl(const char* info, bool cond, std::string msg) {
  if(EXPECT_FALSE( ! cond ))
    throw AssertionException(std::string(info) + "\n" + msg);
}

inline void AssertImpl(const char* info, bool cond, const char* msg) {
  if(EXPECT_FALSE( ! cond ))
    throw AssertionException(std::string(info) + "\n" + msg);
}

inline void AssertImpl(const char* info, bool cond) {
  if(EXPECT_FALSE( ! cond ))
    throw AssertionException(info);
}

#ifdef __GNUC__
inline void UnreachableImpl(const char* info, std::string msg) __attribute__ ((noreturn));
inline void UnreachableImpl(const char* info, const char* msg) __attribute__ ((noreturn));
inline void UnreachableImpl(const char* info) __attribute__ ((noreturn));
#endif /* __GNUC__ */

inline void UnreachableImpl(const char* info, std::string msg) {
  throw UnreachableCodeException(std::string(info) + "\n" + msg);
}

inline void UnreachableImpl(const char* info, const char* msg) {
  throw UnreachableCodeException(std::string(info) + "\n" + msg);
}

inline void UnreachableImpl(const char* info) {
  throw UnreachableCodeException(info);
}

#ifdef __GNUC__
inline void UnhandledImpl(const char* info, std::string msg) __attribute__ ((noreturn));
inline void UnhandledImpl(const char* info, const char* msg) __attribute__ ((noreturn));
inline void UnhandledImpl(const char* info) __attribute__ ((noreturn));
#endif /* __GNUC__ */

inline void UnhandledImpl(const char* info, std::string msg) {
  throw UnhandledCaseException(std::string(info) + "\n" + msg);
}

inline void UnhandledImpl(const char* info, const char* msg) {
  throw UnhandledCaseException(std::string(info) + "\n" + msg);
}

inline void UnhandledImpl(const char* info) {
  throw UnhandledCaseException(info);
}

}/* CVC4 namespace */

#endif /* __CVC4__ASSERT_H */
