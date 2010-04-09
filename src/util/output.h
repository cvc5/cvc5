/*********************                                                        */
/** output.h
 ** Original author: mdeters
 ** Major contributors: none
 ** Minor contributors (to current version): dejan
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.
 **
 ** Output utility classes and functions.
 **/

#include "cvc4_public.h"

#ifndef __CVC4__OUTPUT_H
#define __CVC4__OUTPUT_H

#include <iostream>
#include <string>
#include <cstdio>
#include <cstdarg>
#include <set>

namespace CVC4 {

/**
 * A utility class to provide (essentially) a "/dev/null" streambuf.
 * If debugging support is compiled in, but debugging for
 * e.g. "parser" is off, then Debug("parser") returns a stream
 * attached to a null_streambuf instance so that output is directed to
 * the bit bucket.
 */
class null_streambuf : public std::streambuf {
public:
  /* Overriding overflow() just ensures that EOF isn't returned on the
   * stream.  Perhaps this is not so critical, but recommended; this
   * way the output stream looks like it's functioning, in a non-error
   * state. */
  int overflow(int c) { return c; }
};/* class null_streambuf */

/** A null stream-buffer singleton */
extern null_streambuf null_sb;
/** A null output stream singleton */
extern std::ostream null_os CVC4_PUBLIC;

#ifndef CVC4_MUZZLE

/** The debug output class */
class CVC4_PUBLIC DebugC {
  std::set<std::string> d_tags;
  std::ostream *d_os;

public:
  DebugC(std::ostream* os) : d_os(os) {}

  void operator()(const char* tag, const char* s) {
    if(!d_tags.empty() && d_tags.find(std::string(tag)) != d_tags.end()) {
      *d_os << s;
    }
  }

  void operator()(const char* tag, const std::string& s) {
    if(!d_tags.empty() && d_tags.find(std::string(tag)) != d_tags.end()) {
      *d_os << s;
    }
  }

  void operator()(const std::string& tag, const char* s) {
    if(!d_tags.empty() && d_tags.find(tag) != d_tags.end()) {
      *d_os << s;
    }
  }

  void operator()(const std::string& tag, const std::string& s) {
    if(!d_tags.empty() && d_tags.find(tag) != d_tags.end()) {
      *d_os << s;
    }
  }

  void printf(const char* tag, const char* fmt, ...) __attribute__ ((format(printf, 3, 4)));
  void printf(std::string tag, const char* fmt, ...) __attribute__ ((format(printf, 3, 4)));

  std::ostream& operator()(const char* tag) {
    if(!d_tags.empty() && d_tags.find(std::string(tag)) != d_tags.end()) {
      return *d_os;
    } else {
      return null_os;
    }
  }
  std::ostream& operator()(std::string tag) {
    if(!d_tags.empty() && d_tags.find(tag) != d_tags.end()) {
      return *d_os;
    } else {
      return null_os;
    }
  }
  /**
   * The "Yeting option" - this allows use of Debug() without a tag
   * for temporary (file-only) debugging.
   */
  std::ostream& operator()();

  void on (const char* tag) { d_tags.insert(std::string(tag)); }
  void on (std::string tag) { d_tags.insert(tag);              }
  void off(const char* tag) { d_tags.erase (std::string(tag)); }
  void off(std::string tag) { d_tags.erase (tag);              }

  bool isOn(const char* tag) { return d_tags.find(std::string(tag)) != d_tags.end(); }
  bool isOn(std::string tag) { return d_tags.find(tag) != d_tags.end(); }

  void setStream(std::ostream& os) { d_os = &os; }
};/* class Debug */

/** The debug output singleton */
extern DebugC DebugOut CVC4_PUBLIC;
#ifdef CVC4_DEBUG
#  define Debug DebugOut
#else /* CVC4_DEBUG */
#  define Debug if(0) debugNullCvc4Stream
#endif /* CVC4_DEBUG */

/** The warning output class */
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

/** The warning output singleton */
extern WarningC WarningOut CVC4_PUBLIC;
#define Warning WarningOut

/** The message output class */
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

/** The message output singleton */
extern MessageC MessageOut CVC4_PUBLIC;
#define Message MessageOut

/** The notice output class */
class CVC4_PUBLIC NoticeC {
  std::ostream *d_os;

public:
  NoticeC(std::ostream* os) : d_os(os) {}

  void operator()(const char* s) { *d_os << s; }
  void operator()(std::string s) { *d_os << s; }

  void printf(const char* fmt, ...) __attribute__ ((format(printf, 2, 3)));

  std::ostream& operator()() { return *d_os; }

  void setStream(std::ostream& os) { d_os = &os; }
};/* class Notice */

/** The notice output singleton */
extern NoticeC NoticeOut CVC4_PUBLIC;
#define Notice NoticeOut

/** The chat output class */
class CVC4_PUBLIC ChatC {
  std::ostream *d_os;

public:
  ChatC(std::ostream* os) : d_os(os) {}

  void operator()(const char* s) { *d_os << s; }
  void operator()(std::string s) { *d_os << s; }

  void printf(const char* fmt, ...) __attribute__ ((format(printf, 2, 3)));

  std::ostream& operator()() { return *d_os; }

  void setStream(std::ostream& os) { d_os = &os; }
};/* class Chat */

/** The chat output singleton */
extern ChatC ChatOut CVC4_PUBLIC;
#define Chat ChatOut

/** The trace output class */
class CVC4_PUBLIC TraceC {
  std::ostream *d_os;
  std::set<std::string> d_tags;

public:
  TraceC(std::ostream* os) : d_os(os) {}

  void operator()(const char* tag, const char* s) {
    if(!d_tags.empty() && d_tags.find(std::string(tag)) != d_tags.end()) {
      *d_os << s;
    }
  }

  void operator()(const char* tag, const std::string& s) {
    if(!d_tags.empty() && d_tags.find(std::string(tag)) != d_tags.end()) {
      *d_os << s;
    }
  }

  void operator()(const std::string& tag, const char* s) {
    if(!d_tags.empty() && d_tags.find(tag) != d_tags.end()) {
      *d_os << s;
    }
  }

  void operator()(const std::string& tag, const std::string& s) {
    if(!d_tags.empty() && d_tags.find(tag) != d_tags.end()) {
      *d_os << s;
    }
  }

  void printf(const char* tag, const char* fmt, ...) __attribute__ ((format(printf, 3, 4)));
  void printf(std::string tag, const char* fmt, ...) __attribute__ ((format(printf, 3, 4)));

  std::ostream& operator()(const char* tag) {
    if(!d_tags.empty() && d_tags.find(tag) != d_tags.end()) {
      return *d_os;
    } else {
      return null_os;
    }
  }

  std::ostream& operator()(std::string tag) {
    if(!d_tags.empty() && d_tags.find(tag) != d_tags.end()) {
      return *d_os;
    } else {
      return null_os;
    }
  }

  void on (const char* tag) { d_tags.insert(std::string(tag)); };
  void on (std::string tag) { d_tags.insert(tag);              };
  void off(const char* tag) { d_tags.erase (std::string(tag)); };
  void off(std::string tag) { d_tags.erase (tag);              };

  bool isOn(const char* tag) { return d_tags.find(std::string(tag)) != d_tags.end(); }
  bool isOn(std::string tag) { return d_tags.find(tag) != d_tags.end(); }

  void setStream(std::ostream& os) { d_os = &os; }
};/* class Trace */

/** The trace output singleton */
extern TraceC TraceOut CVC4_PUBLIC;
#ifdef CVC4_TRACING
#  define Trace TraceOut
#else /* CVC4_TRACING */
#  define Trace if(0) debugNullCvc4Stream
#endif /* CVC4_TRACING */

#else /* ! CVC4_MUZZLE */

#  define Debug if(0) debugNullCvc4Stream
#  define Warning if(0) nullCvc4Stream
#  define Message if(0) nullCvc4Stream
#  define Notice if(0) nullCvc4Stream
#  define Chat if(0) nullCvc4Stream
#  define Trace if(0) debugNullCvc4Stream

#endif /* ! CVC4_MUZZLE */

/**
 * Same shape as DebugC/TraceC, but does nothing; designed for
 * compilation of muzzled builds.  None of these should ever be called
 * in muzzled builds, but we offer this to the compiler so it doesn't complain.
 */
class CVC4_PUBLIC NullDebugC {
public:
  NullDebugC() {}
  NullDebugC(std::ostream* os) {}

  void operator()(const char* tag, const char*) {}
  void operator()(const char* tag, std::string) {}
  void operator()(std::string tag, const char*) {}
  void operator()(std::string tag, std::string) {}

  void printf(const char* tag, const char* fmt, ...) __attribute__ ((format(printf, 3, 4))) {}
  void printf(std::string tag, const char* fmt, ...) __attribute__ ((format(printf, 3, 4))) {}

  std::ostream& operator()(const char* tag) { return null_os; }
  std::ostream& operator()(std::string tag) { return null_os; }

  void on (const char* tag) {}
  void on (std::string tag) {}
  void off(const char* tag) {}
  void off(std::string tag) {}

  bool isOn(const char* tag) { return false; }
  bool isOn(std::string tag) { return false; }

  void setStream(std::ostream& os) {}
};/* class NullDebugC */

/**
 * Same shape as WarningC/etc., but does nothing; designed for
 * compilation of muzzled builds.  None of these should ever be called
 * in muzzled builds, but we offer this to the compiler so it doesn't
 * complain. */
class CVC4_PUBLIC NullC {
public:
  NullC() {}
  NullC(std::ostream* os) {}

  void operator()(const char*) {}
  void operator()(std::string) {}

  void printf(const char* fmt, ...) __attribute__ ((format(printf, 2, 3))) {}

  std::ostream& operator()() { return null_os; }

  void setStream(std::ostream& os) {}
};/* class NullC */

extern NullDebugC debugNullCvc4Stream CVC4_PUBLIC;
extern NullC nullCvc4Stream CVC4_PUBLIC;

}/* CVC4 namespace */

#endif /* __CVC4__OUTPUT_H */
