/*********************                                                        */
/*! \file cvc4_assert.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Morgan Deters, Tim King, Paul Meng
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2017 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Assertion utility classes, functions, and exceptions.
 **
 ** Assertion utility classes, functions, and exceptions.  Implementation.
 **/

#include <new>
#include <cstdarg>
#include <cstdio>

#include "base/cvc4_assert.h"
#include "base/output.h"
#include "base/tls.h"

using namespace std;

namespace CVC4 {

#ifdef CVC4_DEBUG
//CVC4_THREAD_LOCAL const char* s_debugLastException = NULL;
#endif /* CVC4_DEBUG */


void AssertionException::construct(const char* header, const char* extra,
                                   const char* function, const char* file,
                                   unsigned line, const char* fmt,
                                   va_list args) {
  // try building the exception msg with a smallish buffer first,
  // then with a larger one if sprintf tells us to.
  int n = 512;
  char* buf;
  buf = new char[n];

  for(;;) {
 
    int size;
    if(extra == NULL) {
      size = snprintf(buf, n, "%s\n%s\n%s:%d\n",
                      header, function, file, line);
    } else {
      size = snprintf(buf, n, "%s\n%s\n%s:%d:\n\n  %s\n",
                      header, function, file, line, extra);
    }

    if(size < n) {
      va_list args_copy;
      va_copy(args_copy, args);
      size += vsnprintf(buf + size, n - size, fmt, args_copy);
      va_end(args_copy);

      if(size < n) {
        break;
      }
    }

    if(size >= n) {
      // try again with a buffer that's large enough
      n = size + 1;
      delete [] buf;
      buf = new char[n];
    }
  }

  setMessage(string(buf));

#ifdef CVC4_DEBUG
  LastExceptionBuffer* buffer = LastExceptionBuffer::getCurrent();
  if(buffer != NULL){
    if(buffer->getContents() == NULL) {
      buffer->setContents(buf);
    }
  }
#endif /* CVC4_DEBUG */
  delete [] buf;
}

void AssertionException::construct(const char* header, const char* extra,
                                   const char* function, const char* file,
                                   unsigned line) {
  // try building the exception msg with a smallish buffer first,
  // then with a larger one if sprintf tells us to.
  int n = 256;
  char* buf;

  for(;;) {
    buf = new char[n];

    int size;
    if(extra == NULL) {
      size = snprintf(buf, n, "%s.\n%s\n%s:%d\n",
                      header, function, file, line);
    } else {
      size = snprintf(buf, n, "%s.\n%s\n%s:%d:\n\n  %s\n",
                      header, function, file, line, extra);
    }

    if(size < n) {
      break;
    } else {
      // try again with a buffer that's large enough
      n = size + 1;
      delete [] buf;
    }
  }

  setMessage(string(buf));


#ifdef CVC4_DEBUG
  LastExceptionBuffer* buffer = LastExceptionBuffer::getCurrent();
  if(buffer != NULL){
    if(buffer->getContents() == NULL) {
      buffer->setContents(buf);
    }
  }
#endif /* CVC4_DEBUG */
  delete [] buf;
}

#ifdef CVC4_DEBUG

/**
 * Special assertion failure handling in debug mode; in non-debug
 * builds, the exception is thrown from the macro.  We factor out this
 * additional logic so as not to bloat the code at every Assert()
 * expansion.
 *
 * Note this name is prefixed with "debug" because it is included in
 * debug builds only; in debug builds, it handles all assertion
 * failures (even those that exist in non-debug builds).
 */
void debugAssertionFailed(const AssertionException& thisException,
                          const char* propagatingException) {
  static CVC4_THREAD_LOCAL bool alreadyFired = false;

  if(__builtin_expect( ( !std::uncaught_exception() ), true ) || alreadyFired) {
    throw thisException;
  }

  alreadyFired = true;

  // propagatingException is the propagating exception, but can be
  // NULL if the propagating exception is not a CVC4::Exception.
  Warning() << "===========================================" << std::endl
            << "An assertion failed during stack unwinding:" << std::endl;
  if(propagatingException != NULL) {
    Warning() << "The propagating exception is:" << std::endl
              << propagatingException << std::endl
              << "===========================================" << std::endl;
    Warning() << "The newly-thrown exception is:" << std::endl;
  } else {
    Warning() << "The propagating exception is unknown." << std::endl;
  }
  Warning() << thisException << std::endl
            << "===========================================" << std::endl;

  terminate();
}

#endif /* CVC4_DEBUG */

}/* CVC4 namespace */
