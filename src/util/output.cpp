/*********************                                                        */
/** output.cpp
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

DebugC   DebugOut(&cout);
WarningC WarningOut(&cerr);
MessageC MessageOut(&cout);
NoticeC  NoticeOut(&cout);
ChatC    ChatOut(&cout);
TraceC   TraceOut(&cout);

void DebugC::printf(const char* tag, const char* fmt, ...) {
  if(d_tags.find(string(tag)) != d_tags.end()) {
    // chop off output after 1024 bytes
    char buf[1024];
    va_list vl;
    va_start(vl, fmt);
    vsnprintf(buf, sizeof(buf), fmt, vl);
    va_end(vl);
    *d_os << buf;
  }
}

void DebugC::printf(string tag, const char* fmt, ...) {
  if(d_tags.find(tag) != d_tags.end()) {
    // chop off output after 1024 bytes
    char buf[1024];
    va_list vl;
    va_start(vl, fmt);
    vsnprintf(buf, sizeof(buf), fmt, vl);
    va_end(vl);
    *d_os << buf;
  }
}

void WarningC::printf(const char* fmt, ...) {
  // chop off output after 1024 bytes
  char buf[1024];
  va_list vl;
  va_start(vl, fmt);
  vsnprintf(buf, sizeof(buf), fmt, vl);
  va_end(vl);
  *d_os << buf;
}

void MessageC::printf(const char* fmt, ...) {
  // chop off output after 1024 bytes
  char buf[1024];
  va_list vl;
  va_start(vl, fmt);
  vsnprintf(buf, sizeof(buf), fmt, vl);
  va_end(vl);
  *d_os << buf;
}

void NoticeC::printf(const char* fmt, ...) {
  // chop off output after 1024 bytes
  char buf[1024];
  va_list vl;
  va_start(vl, fmt);
  vsnprintf(buf, sizeof(buf), fmt, vl);
  va_end(vl);
  *d_os << buf;
}

void ChatC::printf(const char* fmt, ...) {
  // chop off output after 1024 bytes
  char buf[1024];
  va_list vl;
  va_start(vl, fmt);
  vsnprintf(buf, sizeof(buf), fmt, vl);
  va_end(vl);
  *d_os << buf;
}

void TraceC::printf(const char* tag, const char* fmt, ...) {
  if(d_tags.find(string(tag)) != d_tags.end()) {
    // chop off output after 1024 bytes
    char buf[1024];
    va_list vl;
    va_start(vl, fmt);
    vsnprintf(buf, sizeof(buf), fmt, vl);
    va_end(vl);
    *d_os << buf;
  }
}

void TraceC::printf(string tag, const char* fmt, ...) {
  if(d_tags.find(tag) != d_tags.end()) {
    // chop off output after 1024 bytes
    char buf[1024];
    va_list vl;
    va_start(vl, fmt);
    vsnprintf(buf, sizeof(buf), fmt, vl);
    va_end(vl);
    *d_os << buf;
  }
}

#endif /* CVC4_MUZZLE */

}/* CVC4 namespace */
