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

#include <iostream>
#include <string>
#include <set>
#include "util/exception.h"

namespace CVC4 {

class Debug {
  std::set<std::string> d_tags;
  std::ostream &d_out;

public:
  static void operator()(const char* tag, const char*);
  static void operator()(const char* tag, std::string);
  static void operator()(string tag, const char*);
  static void operator()(string tag, std::string);
  static void operator()(const char*);// Yeting option
  static void operator()(std::string);// Yeting option

  static void printf(const char* tag, const char* fmt, ...) __attribute__ ((format(printf, 2, 3)));
  static void printf(const char* tag, std::string fmt, ...) __attribute__ ((format(printf, 2, 3)));
  static void printf(std::string tag, const char* fmt, ...) __attribute__ ((format(printf, 2, 3)));
  static void printf(std::string tag, std::string fmt, ...) __attribute__ ((format(printf, 2, 3)));
  // Yeting option not possible here

  static std::ostream& operator()(const char* tag);
  static std::ostream& operator()(std::string tag);
  static std::ostream& operator()();// Yeting option

  static void on (const char* tag) { d_tags.insert(std::string(tag)); }
  static void on (std::string tag) { d_tags.insert(tag);              }
  static void off(const char* tag) { d_tags.erase (std::string(tag)); }
  static void off(std::string tag) { d_tags.erase (tag);              }

  static void setStream(std::ostream& os) { d_out = os; }
};/* class Debug */


class Warning {
  std::ostream &d_out;

public:
  static void operator()(const char*);
  static void operator()(std::string);

  static void printf(const char* fmt, ...) __attribute__ ((format(printf, 2, 3)));
  static void printf(std::string fmt, ...) __attribute__ ((format(printf, 2, 3)));

  static std::ostream& operator()();

  static void setStream(std::ostream& os) { d_out = os; }
};/* class Warning */


class Notice {
  std::ostream &d_os;

public:
  static void operator()(const char*);
  static void operator()(std::string);

  static void printf(const char* fmt, ...) __attribute__ ((format(printf, 2, 3)));
  static void printf(std::string fmt, ...) __attribute__ ((format(printf, 2, 3)));

  static std::ostream& operator()();

  static void setStream(std::ostream& os) { d_out = os; }
};/* class Notice */


class Chat {
  std::ostream &d_os;

public:
  static void operator()(const char*);
  static void operator()(std::string);

  static void printf(const char* fmt, ...) __attribute__ ((format(printf, 2, 3)));
  static void printf(std::string fmt, ...) __attribute__ ((format(printf, 2, 3)));

  static std::ostream& operator()();

  static void setStream(std::ostream& os) { d_out = os; }
};/* class Chat */


class Trace {
  std::ostream &d_os;

public:
  static void operator()(const char* tag, const char*);
  static void operator()(const char* tag, std::string);
  static void operator()(string tag, const char*);
  static void operator()(string tag, std::string);

  static void printf(const char* tag, const char* fmt, ...) __attribute__ ((format(printf, 2, 3))) {
    va_list vl;
    va_start(vl, fmt);
    vfprintf(buf, 1024, fmt, vl);
    va_end(vl);
  }
  static void printf(const char* tag, std::string fmt, ...) __attribute__ ((format(printf, 2, 3))) {
  }
  static void printf(std::string tag, const char* fmt, ...) __attribute__ ((format(printf, 2, 3))) {
  }
  static void printf(std::string tag, std::string fmt, ...) __attribute__ ((format(printf, 2, 3))) {
  }

  static std::ostream& operator()(const char* tag);
  static std::ostream& operator()(std::string tag);

  static void on (const char* tag) { d_tags.insert(std::string(tag)); };
  static void on (std::string tag) { d_tags.insert(tag);              };
  static void off(const char* tag) { d_tags.erase (std::string(tag)); };
  static void off(std::string tag) { d_tags.erase (tag);              };

  static void setStream(std::ostream& os) { d_out = os; }
};/* class Trace */


}/* CVC4 namespace */

#endif /* __CVC4__OUTPUT_H */
