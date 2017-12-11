/*********************                                                        */
/*! \file exception.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Tim King, Morgan Deters, Paul Meng
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2017 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief CVC4's exception base class and some associated utilities
 **
 ** CVC4's exception base class and some associated utilities.
 **/

#include "base/exception.h"

#include <cstdarg>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <string>

#include "base/cvc4_assert.h"

using namespace std;

namespace CVC4 {

CVC4_THREAD_LOCAL LastExceptionBuffer* LastExceptionBuffer::s_currentBuffer = NULL;

LastExceptionBuffer::LastExceptionBuffer() : d_contents(NULL) {}

LastExceptionBuffer::~LastExceptionBuffer() {
  if(d_contents != NULL){
    free(d_contents);
    d_contents = NULL;
  }
}

void LastExceptionBuffer::setContents(const char* string) {
  if(d_contents != NULL){
    free(d_contents);
    d_contents = NULL;
  }

  if(string != NULL){
    d_contents = strdup(string);
  }
}

const char* IllegalArgumentException::s_header = "Illegal argument detected";

std::string IllegalArgumentException::formatVariadic() {
  return std::string();
}

std::string IllegalArgumentException::formatVariadic(const char* format, ...) {
  va_list args;
  va_start(args, format);

  int n = 512;
  char* buf = NULL;

  for (int i = 0; i < 2; ++i){
    Assert(n > 0);
    if(buf != NULL){
      delete [] buf;
    }
    buf = new char[n];

    va_list args_copy;
    va_copy(args_copy, args);
    int size = vsnprintf(buf, n, format, args);
    va_end(args_copy);

    if(size >= n){
      buf[n-1] = '\0';
      n = size + 1;
    } else {
      break;
    }
  }
  // buf is not NULL is an invariant.
  // buf is also 0 terminated.
  Assert(buf != NULL);
  std::string result(buf);
  delete [] buf;
  va_end(args);
  return result;
}

std::string IllegalArgumentException::format_extra(const char* condStr, const char* argDesc){
  return ( std::string("`") + argDesc + "' is a bad argument"
           + (*condStr == '\0' ? std::string() :
              ( std::string("; expected ") +
                condStr + " to hold" )) );
}

void IllegalArgumentException::construct(const char* header, const char* extra,
                                         const char* function, const char* tail) {
  // try building the exception msg with a smallish buffer first,
  // then with a larger one if sprintf tells us to.
  int n = 512;
  char* buf;

  for(;;) {
    buf = new char[n];

    int size;
    if(extra == NULL) {
      size = snprintf(buf, n, "%s\n%s\n%s",
                      header, function, tail);
    } else {
      size = snprintf(buf, n, "%s\n%s\n\n  %s\n%s",
                      header, function, extra, tail);
    }

    if(size < n) {
      break;
    } else {
      // size >= n
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
  LastExceptionBuffer* buffer = LastExceptionBuffer::getCurrent();
  if(buffer != NULL){
    if(buffer->getContents() == NULL) {
      buffer->setContents(buf);
    }
  }
#endif /* CVC4_DEBUG */
  delete [] buf;
}

} /* namespace CVC4 */
