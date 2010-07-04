/*********************                                                        */
/*! \file output.h
 ** \verbatim
 ** Original author: mdeters
 ** Major contributors: none
 ** Minor contributors (to current version): dejan, cconway
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief Output utility classes and functions.
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

template <class T, class U>
std::ostream& operator<<(std::ostream& out, const std::pair<T, U>& p) CVC4_PUBLIC;

template <class T, class U>
std::ostream& operator<<(std::ostream& out, const std::pair<T, U>& p) {
  return out << "[" << p.first << "," << p.second << "]";
}

/**
 * A utility class to provide (essentially) a "/dev/null" streambuf.
 * If debugging support is compiled in, but debugging for
 * e.g. "parser" is off, then Debug("parser") returns a stream
 * attached to a null_streambuf instance so that output is directed to
 * the bit bucket.
 */
class CVC4_PUBLIC null_streambuf : public std::streambuf {
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

class CVC4_PUBLIC NullCVC4ostream {
public:
  void flush() {}
  bool isConnected() { return false; }
  operator std::ostream&() { return null_os; }

  template <class T>
  NullCVC4ostream& operator<<(T const& t) { return *this; }

  // support manipulators, endl, etc..
  NullCVC4ostream& operator<<(std::ostream& (*pf)(std::ostream&)) { return *this; }
  NullCVC4ostream& operator<<(std::ios& (*pf)(std::ios&)) { return *this; }
  NullCVC4ostream& operator<<(std::ios_base& (*pf)(std::ios_base&)) { return *this; }
};/* class NullCVC4ostream */

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

  NullCVC4ostream operator()(const char* tag) { return NullCVC4ostream(); }
  NullCVC4ostream operator()(std::string tag) { return NullCVC4ostream(); }

  void on (const char* tag) {}
  void on (std::string tag) {}
  void off(const char* tag) {}
  void off(std::string tag) {}

  bool isOn(const char* tag) { return false; }
  bool isOn(std::string tag) { return false; }

  void setStream(std::ostream& os) {}
  std::ostream& getStream() { return null_os; }
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

  NullCVC4ostream operator()() { return NullCVC4ostream(); }

  void setStream(std::ostream& os) {}
  std::ostream& getStream() { return null_os; }
};/* class NullC */

extern NullDebugC debugNullCvc4Stream CVC4_PUBLIC;
extern NullC nullCvc4Stream CVC4_PUBLIC;

#ifndef CVC4_MUZZLE

class CVC4_PUBLIC CVC4ostream {
  std::ostream* d_os;
public:
  CVC4ostream() : d_os(NULL) {}
  CVC4ostream(std::ostream* os) : d_os(os) {}

  void flush() {
    if(d_os != NULL) {
      d_os->flush();
    }
  }

  bool isConnected() { return d_os != NULL; }
  operator std::ostream&() { return isConnected() ? *d_os : null_os; }

  template <class T>
  CVC4ostream& operator<<(T const& t) {
    if(d_os != NULL) {
      d_os = &(*d_os << t);
    }
    return *this;
  }

  // support manipulators, endl, etc..
  CVC4ostream& operator<<(std::ostream& (*pf)(std::ostream&)) {
    if(d_os != NULL) {
      d_os = &(*d_os << pf);
    }
    return *this;
  }
  CVC4ostream& operator<<(std::ios& (*pf)(std::ios&)) {
    if(d_os != NULL) {
      d_os = &(*d_os << pf);
    }
    return *this;
  }
  CVC4ostream& operator<<(std::ios_base& (*pf)(std::ios_base&)) {
    if(d_os != NULL) {
      d_os = &(*d_os << pf);
    }
    return *this;
  }

};/* class CVC4ostream */

/** The debug output class */
class CVC4_PUBLIC DebugC {
  std::set<std::string> d_tags;
  std::ostream* d_os;

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

  CVC4ostream operator()(const char* tag) {
    if(!d_tags.empty() && d_tags.find(std::string(tag)) != d_tags.end()) {
      return CVC4ostream(d_os);
    } else {
      return CVC4ostream();
    }
  }
  CVC4ostream operator()(std::string tag) {
    if(!d_tags.empty() && d_tags.find(tag) != d_tags.end()) {
      return CVC4ostream(d_os);
    } else {
      return CVC4ostream();
    }
  }
  /**
   * The "Yeting option" - this allows use of Debug() without a tag
   * for temporary (file-only) debugging.
   */
  CVC4ostream operator()();

  void on (const char* tag) { d_tags.insert(std::string(tag)); }
  void on (std::string tag) { d_tags.insert(tag);              }
  void off(const char* tag) { d_tags.erase (std::string(tag)); }
  void off(std::string tag) { d_tags.erase (tag);              }

  bool isOn(const char* tag) { return d_tags.find(std::string(tag)) != d_tags.end(); }
  bool isOn(std::string tag) { return d_tags.find(tag) != d_tags.end(); }

  void setStream(std::ostream& os) { d_os = &os; }
  std::ostream& getStream() { return *d_os; }
};/* class DebugC */

/** The warning output class */
class CVC4_PUBLIC WarningC {
  std::ostream* d_os;

public:
  WarningC(std::ostream* os) : d_os(os) {}

  void operator()(const char* s) { *d_os << s; }
  void operator()(std::string s) { *d_os << s; }

  void printf(const char* fmt, ...) __attribute__ ((format(printf, 2, 3)));

  CVC4ostream operator()() { return CVC4ostream(d_os); }

  void setStream(std::ostream& os) { d_os = &os; }
  std::ostream& getStream() { return *d_os; }
};/* class WarningC */

/** The message output class */
class CVC4_PUBLIC MessageC {
  std::ostream* d_os;

public:
  MessageC(std::ostream* os) : d_os(os) {}

  void operator()(const char* s) { *d_os << s; }
  void operator()(std::string s) { *d_os << s; }

  void printf(const char* fmt, ...) __attribute__ ((format(printf, 2, 3)));

  CVC4ostream operator()() { return CVC4ostream(d_os); }

  void setStream(std::ostream& os) { d_os = &os; }
  std::ostream& getStream() { return *d_os; }
};/* class MessageC */

/** The notice output class */
class CVC4_PUBLIC NoticeC {
  std::ostream* d_os;

public:
  NoticeC(std::ostream* os) : d_os(os) {}

  void operator()(const char* s) { *d_os << s; }
  void operator()(std::string s) { *d_os << s; }

  void printf(const char* fmt, ...) __attribute__ ((format(printf, 2, 3)));

  CVC4ostream operator()() { return CVC4ostream(d_os); }

  void setStream(std::ostream& os) { d_os = &os; }
  std::ostream& getStream() { return *d_os; }
};/* class NoticeC */

/** The chat output class */
class CVC4_PUBLIC ChatC {
  std::ostream* d_os;

public:
  ChatC(std::ostream* os) : d_os(os) {}

  void operator()(const char* s) { *d_os << s; }
  void operator()(std::string s) { *d_os << s; }

  void printf(const char* fmt, ...) __attribute__ ((format(printf, 2, 3)));

  CVC4ostream operator()() { return CVC4ostream(d_os); }

  void setStream(std::ostream& os) { d_os = &os; }
  std::ostream& getStream() { return *d_os; }
};/* class ChatC */

/** The trace output class */
class CVC4_PUBLIC TraceC {
  std::ostream* d_os;
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

  CVC4ostream operator()(const char* tag) {
    if(!d_tags.empty() && d_tags.find(tag) != d_tags.end()) {
      return CVC4ostream(d_os);
    } else {
      return CVC4ostream();
    }
  }

  CVC4ostream operator()(std::string tag) {
    if(!d_tags.empty() && d_tags.find(tag) != d_tags.end()) {
      return CVC4ostream(d_os);
    } else {
      return CVC4ostream();
    }
  }

  void on (const char* tag) { d_tags.insert(std::string(tag)); };
  void on (std::string tag) { d_tags.insert(tag);              };
  void off(const char* tag) { d_tags.erase (std::string(tag)); };
  void off(std::string tag) { d_tags.erase (tag);              };

  bool isOn(const char* tag) { return d_tags.find(std::string(tag)) != d_tags.end(); }
  bool isOn(std::string tag) { return d_tags.find(tag) != d_tags.end(); }

  void setStream(std::ostream& os) { d_os = &os; }
  std::ostream& getStream() { return *d_os; }
};/* class TraceC */

/** The debug output singleton */
#ifdef CVC4_DEBUG
extern DebugC Debug CVC4_PUBLIC;
#else /* CVC4_DEBUG */
extern NullDebugC Debug CVC4_PUBLIC;
#endif /* CVC4_DEBUG */

/** The warning output singleton */
extern WarningC Warning CVC4_PUBLIC;
/** The message output singleton */
extern MessageC Message CVC4_PUBLIC;
/** The notice output singleton */
extern NoticeC Notice CVC4_PUBLIC;
/** The chat output singleton */
extern ChatC Chat CVC4_PUBLIC;

/** The trace output singleton */
#ifdef CVC4_TRACING
extern TraceC Trace CVC4_PUBLIC;
#else /* CVC4_TRACING */
extern NullDebugC Trace CVC4_PUBLIC;
#endif /* CVC4_TRACING */

#ifdef CVC4_DEBUG

class CVC4_PUBLIC ScopedDebug {
  std::string d_tag;
  bool d_oldSetting;

public:

  ScopedDebug(std::string tag, bool newSetting = true) :
    d_tag(tag) {
    d_oldSetting = Debug.isOn(d_tag);
    if(newSetting) {
      Debug.on(d_tag);
    } else {
      Debug.off(d_tag);
    }
  }

  ScopedDebug(const char* tag, bool newSetting = true) :
    d_tag(tag) {
    d_oldSetting = Debug.isOn(d_tag);
    if(newSetting) {
      Debug.on(d_tag);
    } else {
      Debug.off(d_tag);
    }
  }

  ~ScopedDebug() {
    if(d_oldSetting) {
      Debug.on(d_tag);
    } else {
      Debug.off(d_tag);
    }
  }
};/* class ScopedDebug */

#else /* CVC4_DEBUG */

class CVC4_PUBLIC ScopedDebug {
public:
  ScopedDebug(std::string tag, bool newSetting = true) {}
  ScopedDebug(const char* tag, bool newSetting = true) {}
};/* class ScopedDebug */

#endif /* CVC4_DEBUG */

#ifdef CVC4_TRACING

class CVC4_PUBLIC ScopedTrace {
  std::string d_tag;
  bool d_oldSetting;

public:

  ScopedTrace(std::string tag, bool newSetting = true) :
    d_tag(tag) {
    d_oldSetting = Trace.isOn(d_tag);
    if(newSetting) {
      Trace.on(d_tag);
    } else {
      Trace.off(d_tag);
    }
  }

  ScopedTrace(const char* tag, bool newSetting = true) :
    d_tag(tag) {
    d_oldSetting = Trace.isOn(d_tag);
    if(newSetting) {
      Trace.on(d_tag);
    } else {
      Trace.off(d_tag);
    }
  }

  ~ScopedTrace() {
    if(d_oldSetting) {
      Trace.on(d_tag);
    } else {
      Trace.off(d_tag);
    }
  }
};/* class ScopedTrace */

#else /* CVC4_TRACING */

class CVC4_PUBLIC ScopedTrace {
public:
  ScopedTrace(std::string tag, bool newSetting = true) {}
  ScopedTrace(const char* tag, bool newSetting = true) {}
};/* class ScopedTrace */

#endif /* CVC4_TRACING */

#else /* ! CVC4_MUZZLE */

class CVC4_PUBLIC ScopedDebug {
public:
  ScopedDebug(std::string tag, bool newSetting = true) {}
  ScopedDebug(const char* tag, bool newSetting = true) {}
};/* class ScopedDebug */

class CVC4_PUBLIC ScopedTrace {
public:
  ScopedTrace(std::string tag, bool newSetting = true) {}
  ScopedTrace(const char* tag, bool newSetting = true) {}
};/* class ScopedTrace */

extern NullDebugC Debug CVC4_PUBLIC;
extern NullC Warning CVC4_PUBLIC;
extern NullC Warning CVC4_PUBLIC;
extern NullC Message CVC4_PUBLIC;
extern NullC Notice CVC4_PUBLIC;
extern NullC Chat CVC4_PUBLIC;
extern NullDebugC Trace CVC4_PUBLIC;

#endif /* ! CVC4_MUZZLE */

// don't use debugTagIsOn() anymore, use Debug.isOn()
inline bool debugTagIsOn(std::string tag) __attribute__((__deprecated__));
inline bool debugTagIsOn(std::string tag) {
#if defined(CVC4_DEBUG) && !defined(CVC4_MUZZLE)
  return Debug.isOn(tag);
#else /* CVC4_DEBUG && !CVC4_MUZZLE */
  return false;
#endif /* CVC4_DEBUG && !CVC4_MUZZLE */
}/* debugTagIsOn() */

}/* CVC4 namespace */

#endif /* __CVC4__OUTPUT_H */
