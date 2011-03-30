/*********************                                                        */
/*! \file output.cpp
 ** \verbatim
 ** Original author: mdeters
 ** Major contributors: none
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010, 2011  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief Output utility classes and functions.
 **
 ** Output utility classes and functions.
 **/

#include <iostream>

#include "util/output.h"

using namespace std;

namespace CVC4 {

/* Definitions of the declared globals from output.h... */

null_streambuf null_sb;
ostream null_os(&null_sb);

NullDebugC debugNullCvc4Stream CVC4_PUBLIC;
NullC nullCvc4Stream CVC4_PUBLIC;

#ifndef CVC4_MUZZLE

DebugC DebugChannel CVC4_PUBLIC (&cout);
WarningC Warning CVC4_PUBLIC (&cerr);
MessageC Message CVC4_PUBLIC (&cout);
NoticeC Notice CVC4_PUBLIC (&cout);
ChatC Chat CVC4_PUBLIC (&cout);
TraceC TraceChannel CVC4_PUBLIC (&cout);

int DebugC::printf(const char* tag, const char* fmt, ...) {
  if(d_tags.find(string(tag)) == d_tags.end()) {
    return 0;
  }

  // chop off output after 1024 bytes
  char buf[1024];
  va_list vl;
  va_start(vl, fmt);
  int retval = vsnprintf(buf, sizeof(buf), fmt, vl);
  va_end(vl);
  *d_os << buf;
  return retval;
}

int DebugC::printf(std::string tag, const char* fmt, ...) {
  if(d_tags.find(tag) == d_tags.end()) {
    return 0;
  }

  // chop off output after 1024 bytes
  char buf[1024];
  va_list vl;
  va_start(vl, fmt);
  int retval = vsnprintf(buf, sizeof(buf), fmt, vl);
  va_end(vl);
  *d_os << buf;
  return retval;
}

int WarningC::printf(const char* fmt, ...) {
  // chop off output after 1024 bytes
  char buf[1024];
  va_list vl;
  va_start(vl, fmt);
  int retval = vsnprintf(buf, sizeof(buf), fmt, vl);
  va_end(vl);
  *d_os << buf;
  return retval;
}

int MessageC::printf(const char* fmt, ...) {
  // chop off output after 1024 bytes
  char buf[1024];
  va_list vl;
  va_start(vl, fmt);
  int retval = vsnprintf(buf, sizeof(buf), fmt, vl);
  va_end(vl);
  *d_os << buf;
  return retval;
}

int NoticeC::printf(const char* fmt, ...) {
  // chop off output after 1024 bytes
  char buf[1024];
  va_list vl;
  va_start(vl, fmt);
  int retval = vsnprintf(buf, sizeof(buf), fmt, vl);
  va_end(vl);
  *d_os << buf;
  return retval;
}

int ChatC::printf(const char* fmt, ...) {
  // chop off output after 1024 bytes
  char buf[1024];
  va_list vl;
  va_start(vl, fmt);
  int retval = vsnprintf(buf, sizeof(buf), fmt, vl);
  va_end(vl);
  *d_os << buf;
  return retval;
}

int TraceC::printf(const char* tag, const char* fmt, ...) {
  if(d_tags.find(string(tag)) == d_tags.end()) {
    return 0;
  }

  // chop off output after 1024 bytes
  char buf[1024];
  va_list vl;
  va_start(vl, fmt);
  int retval = vsnprintf(buf, sizeof(buf), fmt, vl);
  va_end(vl);
  *d_os << buf;
  return retval;
}

int TraceC::printf(std::string tag, const char* fmt, ...) {
  if(d_tags.find(tag) == d_tags.end()) {
    return 0;
  }

  // chop off output after 1024 bytes
  char buf[1024];
  va_list vl;
  va_start(vl, fmt);
  int retval = vsnprintf(buf, sizeof(buf), fmt, vl);
  va_end(vl);
  *d_os << buf;
  return retval;
}

#else /* ! CVC4_MUZZLE */

NullDebugC Debug CVC4_PUBLIC;
NullC Warning CVC4_PUBLIC;
NullC Message CVC4_PUBLIC;
NullC Notice CVC4_PUBLIC;
NullC Chat CVC4_PUBLIC;
NullDebugC Trace CVC4_PUBLIC;

#endif /* ! CVC4_MUZZLE */

}/* CVC4 namespace */
