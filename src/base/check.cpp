/*********************                                                        */
/*! \file check.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Mathias Preiner, Morgan Deters, Tim King
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Assertion utility classes, functions and macros.
 **
 ** Implementation of assertion utility classes, functions and macros.
 **/

#include "base/check.h"

#include <cstdlib>
#include <iostream>

namespace CVC4 {

FatalStream::FatalStream(const char* function, const char* file, int line)
{
  stream() << "Fatal failure within " << function << " at " << file << ":"
           << line << "\n";
}

FatalStream::~FatalStream()
{
  Flush();
  abort();
}

std::ostream& FatalStream::stream() { return std::cerr; }

void FatalStream::Flush()
{
  stream() << std::endl;
  stream().flush();
}

void AssertArgumentException::construct(const char* header,
                                        const char* extra,
                                        const char* function,
                                        const char* file,
                                        unsigned line,
                                        const char* fmt,
                                        va_list args)
{
  // try building the exception msg with a smallish buffer first,
  // then with a larger one if sprintf tells us to.
  int n = 512;
  char* buf;
  buf = new char[n];

  for (;;)
  {
    int size;
    if (extra == NULL)
    {
      size = snprintf(buf, n, "%s\n%s\n%s:%d\n", header, function, file, line);
    }
    else
    {
      size = snprintf(buf,
                      n,
                      "%s\n%s\n%s:%d:\n\n  %s\n",
                      header,
                      function,
                      file,
                      line,
                      extra);
    }

    if (size < n)
    {
      va_list args_copy;
      va_copy(args_copy, args);
      size += vsnprintf(buf + size, n - size, fmt, args_copy);
      va_end(args_copy);

      if (size < n)
      {
        break;
      }
    }

    if (size >= n)
    {
      // try again with a buffer that's large enough
      n = size + 1;
      delete[] buf;
      buf = new char[n];
    }
  }

  setMessage(std::string(buf));

#ifdef CVC4_DEBUG
  LastExceptionBuffer* buffer = LastExceptionBuffer::getCurrent();
  if (buffer != NULL)
  {
    if (buffer->getContents() == NULL)
    {
      buffer->setContents(buf);
    }
  }
#endif /* CVC4_DEBUG */
  delete[] buf;
}

void AssertArgumentException::construct(const char* header,
                                        const char* extra,
                                        const char* function,
                                        const char* file,
                                        unsigned line)
{
  // try building the exception msg with a smallish buffer first,
  // then with a larger one if sprintf tells us to.
  int n = 256;
  char* buf;

  for (;;)
  {
    buf = new char[n];

    int size;
    if (extra == NULL)
    {
      size = snprintf(buf, n, "%s.\n%s\n%s:%d\n", header, function, file, line);
    }
    else
    {
      size = snprintf(buf,
                      n,
                      "%s.\n%s\n%s:%d:\n\n  %s\n",
                      header,
                      function,
                      file,
                      line,
                      extra);
    }

    if (size < n)
    {
      break;
    }
    else
    {
      // try again with a buffer that's large enough
      n = size + 1;
      delete[] buf;
    }
  }

  setMessage(std::string(buf));

#ifdef CVC4_DEBUG
  LastExceptionBuffer* buffer = LastExceptionBuffer::getCurrent();
  if (buffer != NULL)
  {
    if (buffer->getContents() == NULL)
    {
      buffer->setContents(buf);
    }
  }
#endif /* CVC4_DEBUG */
  delete[] buf;
}

AssertArgumentException::AssertArgumentException(const char* condStr,
                                                 const char* argDesc,
                                                 const char* function,
                                                 const char* file,
                                                 unsigned line,
                                                 const char* fmt,
                                                 ...)
    : Exception()
{
  va_list args;
  va_start(args, fmt);
  construct("Illegal argument detected",
            (std::string("`") + argDesc + "' is a bad argument; expected "
             + condStr + " to hold")
                .c_str(),
            function,
            file,
            line,
            fmt,
            args);
  va_end(args);
}

AssertArgumentException::AssertArgumentException(const char* condStr,
                                                 const char* argDesc,
                                                 const char* function,
                                                 const char* file,
                                                 unsigned line)
    : Exception()
{
  construct("Illegal argument detected",
            (std::string("`") + argDesc + "' is a bad argument; expected "
             + condStr + " to hold")
                .c_str(),
            function,
            file,
            line);
}

}  // namespace CVC4
