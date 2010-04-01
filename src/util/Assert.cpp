/*********************                                                        */
/** Assert.cpp
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
 ** Assertion utility classes, functions, and exceptions.  Implementation.
 **/

#include <new>
#include <cstdarg>
#include <cstdio>

#include "util/Assert.h"
#include "util/exception.h"

using namespace std;

namespace CVC4 {

#ifdef CVC4_DEBUG
__thread CVC4_PUBLIC const char* s_debugAssertionFailure = NULL;
#endif /* CVC4_DEBUG */

void AssertionException::construct(const char* header, const char* extra,
                                   const char* function, const char* file,
                                   unsigned line, const char* fmt,
                                   va_list args) {
  // try building the exception msg with a smallish buffer first,
  // then with a larger one if sprintf tells us to.
  int n = 512;
  char* buf;

  for(;;) {
    buf = new char[n];

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
      size += vsnprintf(buf + size, n - size, fmt, args);
      va_end(args_copy);

      if(size < n) {
        break;
      }
    }

    if(size >= n) {
      // try again with a buffer that's large enough
      n = size + 1;
      delete [] buf;
    }
  }

  setMessage(string(buf));

#ifdef CVC4_DEBUG
  // we leak buf[] but only in debug mode with assertions failing
  s_debugAssertionFailure = buf;
#else /* CVC4_DEBUG */
  delete [] buf;
#endif /* CVC4_DEBUG */
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
  // we leak buf[] but only in debug mode with assertions failing
  s_debugAssertionFailure = buf;
#else /* CVC4_DEBUG */
  delete [] buf;
#endif /* CVC4_DEBUG */
}

}/* CVC4 namespace */
