/*********************                                           -*- C++ -*-  */
/** output.h
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009 The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.
 **
 ** Output utility classes and functions.
 **/

#ifndef __CVC4__OUTPUT_H
#define __CVC4__OUTPUT_H

#include "cvc4_config.h"

#include <iostream>
#include <string>
#include <cstdio>
#include <cstdarg>
#include <set>

#include "util/exception.h"

namespace CVC4 {

class null_streambuf : public std::streambuf {
public:
  int overflow(int c) { return c; }
};/* class null_streambuf */

extern null_streambuf null_sb;
extern std::ostream null_os CVC4_PUBLIC;

class CVC4_PUBLIC DebugC {
  std::set<std::string> d_tags;
  std::ostream *d_os;

public:
  DebugC(std::ostream* os) : d_os(os) {}

  void operator()(const char* tag, const char*);
  void operator()(const char* tag, std::string);
  void operator()(std::string tag, const char*);
  void operator()(std::string tag, std::string);
  //void operator()(const char*);// Yeting option
  //void operator()(std::string);// Yeting option

  static void printf(const char* tag, const char* fmt, ...) __attribute__ ((format(printf, 2, 3)));
  static void printf(std::string tag, const char* fmt, ...) __attribute__ ((format(printf, 2, 3)));
  // Yeting option not possible here

  std::ostream& operator()(const char* tag) {
    if(d_tags.find(tag) != d_tags.end())
      return *d_os;
    else return null_os;
  }
  std::ostream& operator()(std::string tag) {
    if(d_tags.find(tag) != d_tags.end())
      return *d_os;
    else return null_os;
  }
  std::ostream& operator()();// Yeting option

  void on (const char* tag) { d_tags.insert(std::string(tag)); }
  void on (std::string tag) { d_tags.insert(tag);              }
  void off(const char* tag) { d_tags.erase (std::string(tag)); }
  void off(std::string tag) { d_tags.erase (tag);              }

  void setStream(std::ostream& os) { d_os = &os; }
};/* class Debug */

extern DebugC Debug CVC4_PUBLIC;

class CVC4_PUBLIC WarningC {
  std::ostream *d_os;

public:
  WarningC(std::ostream* os) : d_os(os) {}

  void operator()(const char* s) { *d_os << s; }
  void operator()(std::string s) { *d_os << s; }

  void printf(const char* fmt, ...) __attribute__ ((format(printf, 2, 3)));

  std::ostream& operator()() { return *d_os; }

  void setStream(std::ostream& os) { d_os = &os; }
};/* class Warning */

extern WarningC Warning CVC4_PUBLIC;

class CVC4_PUBLIC MessageC {
  std::ostream *d_os;

public:
  MessageC(std::ostream* os) : d_os(os) {}

  void operator()(const char* s) { *d_os << s; }
  void operator()(std::string s) { *d_os << s; }

  void printf(const char* fmt, ...) __attribute__ ((format(printf, 2, 3)));

  std::ostream& operator()() { return *d_os; }

  void setStream(std::ostream& os) { d_os = &os; }
};/* class Message */

extern MessageC Message CVC4_PUBLIC;

class CVC4_PUBLIC NoticeC {
  std::ostream *d_os;

public:
  NoticeC(std::ostream* os) : d_os(os) {}

  void operator()(const char*);
  void operator()(std::string);

  void printf(const char* fmt, ...) __attribute__ ((format(printf, 2, 3)));

  std::ostream& operator()() { return *d_os; }

  void setStream(std::ostream& os) { d_os = &os; }
};/* class Notice */

extern NoticeC Notice CVC4_PUBLIC;

class CVC4_PUBLIC ChatC {
  std::ostream *d_os;

public:
  ChatC(std::ostream* os) : d_os(os) {}

  void operator()(const char*);
  void operator()(std::string);

  void printf(const char* fmt, ...) __attribute__ ((format(printf, 2, 3)));

  std::ostream& operator()() { return *d_os; }

  void setStream(std::ostream& os) { d_os = &os; }
};/* class Chat */

extern ChatC Chat CVC4_PUBLIC;

class CVC4_PUBLIC TraceC {
  std::ostream *d_os;
  std::set<std::string> d_tags;

public:
  TraceC(std::ostream* os) : d_os(os) {}

  void operator()(const char* tag, const char*);
  void operator()(const char* tag, std::string);
  void operator()(std::string tag, const char*);
  void operator()(std::string tag, std::string);

  void printf(const char* tag, const char* fmt, ...) __attribute__ ((format(printf, 3, 4))) {
    char buf[1024];
    va_list vl;
    va_start(vl, fmt);
    vsnprintf(buf, sizeof(buf), fmt, vl);
    va_end(vl);
    *d_os << buf;
  }
  void printf(std::string tag, const char* fmt, ...) __attribute__ ((format(printf, 3, 4))) {
  }

  std::ostream& operator()(const char* tag) {
    if(d_tags.find(tag) != d_tags.end())
      return *d_os;
    else return null_os;
  }

  std::ostream& operator()(std::string tag) {
    if(d_tags.find(tag) != d_tags.end())
      return *d_os;
    else return null_os;
  }

  void on (const char* tag) { d_tags.insert(std::string(tag)); };
  void on (std::string tag) { d_tags.insert(tag);              };
  void off(const char* tag) { d_tags.erase (std::string(tag)); };
  void off(std::string tag) { d_tags.erase (tag);              };

  void setStream(std::ostream& os) { d_os = &os; }
};/* class Trace */

extern TraceC Trace CVC4_PUBLIC;

}/* CVC4 namespace */

#endif /* __CVC4__OUTPUT_H */
