/*********************                                                        */
/*! \file exception.cpp
 ** \verbatim
 ** Original author: Morgan Deters
 ** Major contributors: none
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2013  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief CVC4's exception base class and some associated utilities
 **
 ** CVC4's exception base class and some associated utilities.
 **/

#include "util/exception.h"
#include <string>
#include <cstdio>
#include <cstdlib>
#include <cstdarg>
#include "util/cvc4_assert.h"

using namespace std;
using namespace CVC4;

void IllegalArgumentException::construct(const char* header, const char* extra,
                                         const char* function, const char* fmt,
                                         va_list args) {
  // try building the exception msg with a smallish buffer first,
  // then with a larger one if sprintf tells us to.
  int n = 512;
  char* buf;

  for(;;) {
    buf = new char[n];

    int size;
    if(extra == NULL) {
      size = snprintf(buf, n, "%s\n%s\n",
                      header, function);
    } else {
      size = snprintf(buf, n, "%s\n%s\n\n  %s\n",
                      header, function, extra);
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
    }
  }

  setMessage(string(buf));

#ifdef CVC4_DEBUG
  if(s_debugLastException == NULL) {
    // we leak buf[] but only in debug mode with assertions failing
    s_debugLastException = buf;
  }
#else /* CVC4_DEBUG */
  delete [] buf;
#endif /* CVC4_DEBUG */
}

void IllegalArgumentException::construct(const char* header, const char* extra,
                                         const char* function) {
  // try building the exception msg with a smallish buffer first,
  // then with a larger one if sprintf tells us to.
  int n = 256;
  char* buf;

  for(;;) {
    buf = new char[n];

    int size;
    if(extra == NULL) {
      size = snprintf(buf, n, "%s.\n%s\n",
                      header, function);
    } else {
      size = snprintf(buf, n, "%s.\n%s\n\n  %s\n",
                      header, function, extra);
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
  if(s_debugLastException == NULL) {
    // we leak buf[] but only in debug mode with assertions failing
    s_debugLastException = buf;
  }
#else /* CVC4_DEBUG */
  delete [] buf;
#endif /* CVC4_DEBUG */
}
