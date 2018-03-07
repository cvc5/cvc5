/*********************                                                        */
/*! \file output.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Morgan Deters, Tim King, Dejan Jovanovic
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2017 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Output utility classes and functions
 **
 ** Output utility classes and functions.
 **/

#include "cvc4_private_library.h"

#ifndef __CVC4__OUTPUT_H
#define __CVC4__OUTPUT_H

#include <ios>
#include <iostream>
#include <streambuf>
#include <string>
#include <cstdio>
#include <cstdarg>
#include <set>
#include <utility>

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
 int overflow(int c) override { return c; }
};/* class null_streambuf */

/** A null stream-buffer singleton */
extern null_streambuf null_sb;
/** A null output stream singleton */
extern std::ostream null_os CVC4_PUBLIC;

class CVC4_PUBLIC CVC4ostream {
  static const std::string s_tab;
  static const int s_indentIosIndex;

  /** The underlying ostream */
  std::ostream* d_os;
  /** Are we in the first column? */
  bool d_firstColumn;

  /** The endl manipulator (why do we need to keep this?) */
  std::ostream& (*const d_endl)(std::ostream&);

  // do not allow use
  CVC4ostream& operator=(const CVC4ostream&);

public:
  CVC4ostream() :
    d_os(NULL),
    d_firstColumn(false),
    d_endl(&std::endl) {
  }
  explicit CVC4ostream(std::ostream* os) :
    d_os(os),
    d_firstColumn(true),
    d_endl(&std::endl) {
  }

  void pushIndent() {
    if(d_os != NULL) {
      ++d_os->iword(s_indentIosIndex);
    }
  }
  void popIndent() {
    if(d_os != NULL) {
      long& indent = d_os->iword(s_indentIosIndex);
      if(indent > 0) {
        --indent;
      }
    }
  }

  CVC4ostream& flush() {
    if(d_os != NULL) {
      d_os->flush();
    }
    return *this;
  }

  bool isConnected() const { return d_os != NULL; }
  operator std::ostream&() const { return isConnected() ? *d_os : null_os; }

  std::ostream* getStreamPointer() const { return d_os; }

  template <class T>
  CVC4ostream& operator<<(T const& t) CVC4_PUBLIC;

  // support manipulators, endl, etc..
  CVC4ostream& operator<<(std::ostream& (*pf)(std::ostream&)) {
    if(d_os != NULL) {
      d_os = &(*d_os << pf);

      if(pf == d_endl) {
        d_firstColumn = true;
      }
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
  CVC4ostream& operator<<(CVC4ostream& (*pf)(CVC4ostream&)) {
    return pf(*this);
  }
};/* class CVC4ostream */

inline CVC4ostream& push(CVC4ostream& stream) {
  stream.pushIndent();
  return stream;
}

inline CVC4ostream& pop(CVC4ostream& stream) {
  stream.popIndent();
  return stream;
}

template <class T>
CVC4ostream& CVC4ostream::operator<<(T const& t) {
  if(d_os != NULL) {
    if(d_firstColumn) {
      d_firstColumn = false;
      long indent = d_os->iword(s_indentIosIndex);
      for(long i = 0; i < indent; ++i) {
        d_os = &(*d_os << s_tab);
      }
    }
    d_os = &(*d_os << t);
  }
  return *this;
}

/**
 * Does nothing; designed for compilation of non-debug/non-trace
 * builds.  None of these should ever be called in such builds, but we
 * offer this to the compiler so it doesn't complain.
 */
class CVC4_PUBLIC NullC {
public:
 operator bool() const { return false; }
 operator CVC4ostream() const { return CVC4ostream(); }
 operator std::ostream&() const { return null_os; }
};/* class NullC */

extern NullC nullCvc4Stream CVC4_PUBLIC;

/** The debug output class */
class CVC4_PUBLIC DebugC {
  std::set<std::string> d_tags;
  std::ostream* d_os;

public:
  explicit DebugC(std::ostream* os) : d_os(os) {}

  CVC4ostream operator()(const std::string& tag) const
  {
    if(!d_tags.empty() && d_tags.find(tag) != d_tags.end()) {
      return CVC4ostream(d_os);
    } else {
      return CVC4ostream();
    }
  }

  bool on(const std::string& tag)
  {
    d_tags.insert(tag);
    return true;
  }
  bool off(const std::string& tag)
  {
    d_tags.erase(tag);
    return false;
  }
  bool off()                { d_tags.clear(); return false; }

  bool isOn(const std::string& tag) const
  {
    return d_tags.find(tag) != d_tags.end();
  }

  std::ostream& setStream(std::ostream* os) { d_os = os; return *os; }
  std::ostream& getStream() const { return *d_os; }
  std::ostream* getStreamPointer() const { return d_os; }
};/* class DebugC */

/** The warning output class */
class CVC4_PUBLIC WarningC {
  std::set<std::pair<std::string, size_t> > d_alreadyWarned;
  std::ostream* d_os;

public:
  explicit WarningC(std::ostream* os) : d_os(os) {}

  CVC4ostream operator()() const { return CVC4ostream(d_os); }

  std::ostream& setStream(std::ostream* os) { d_os = os; return *d_os; }
  std::ostream& getStream() const { return *d_os; }
  std::ostream* getStreamPointer() const { return d_os; }

  bool isOn() const { return d_os != &null_os; }

  // This function supports the WarningOnce() macro, which allows you
  // to easily indicate that a warning should be emitted, but only
  // once for a given run of CVC4.
  bool warnOnce(const std::string& file, size_t line)
  {
    std::pair<std::string, size_t> pr = std::make_pair(file, line);
    if(d_alreadyWarned.find(pr) != d_alreadyWarned.end()) {
      // signal caller not to warn again
      return false;
    }

    // okay warn this time, but don't do it again
    d_alreadyWarned.insert(pr);
    return true;
  }

};/* class WarningC */

/** The message output class */
class CVC4_PUBLIC MessageC {
  std::ostream* d_os;

public:
  explicit MessageC(std::ostream* os) : d_os(os) {}

  CVC4ostream operator()() const { return CVC4ostream(d_os); }

  std::ostream& setStream(std::ostream* os) { d_os = os; return *d_os; }
  std::ostream& getStream() const { return *d_os; }
  std::ostream* getStreamPointer() const { return d_os; }

  bool isOn() const { return d_os != &null_os; }
};/* class MessageC */

/** The notice output class */
class CVC4_PUBLIC NoticeC {
  std::ostream* d_os;

public:
  explicit NoticeC(std::ostream* os) : d_os(os) {}

  CVC4ostream operator()() const { return CVC4ostream(d_os); }

  std::ostream& setStream(std::ostream* os) { d_os = os; return *d_os; }
  std::ostream& getStream() const { return *d_os; }
  std::ostream* getStreamPointer() const { return d_os; }

  bool isOn() const { return d_os != &null_os; }
};/* class NoticeC */

/** The chat output class */
class CVC4_PUBLIC ChatC {
  std::ostream* d_os;

public:
  explicit ChatC(std::ostream* os) : d_os(os) {}

  CVC4ostream operator()() const { return CVC4ostream(d_os); }

  std::ostream& setStream(std::ostream* os) { d_os = os; return *d_os; }
  std::ostream& getStream() const { return *d_os; }
  std::ostream* getStreamPointer() const { return d_os; }

  bool isOn() const { return d_os != &null_os; }
};/* class ChatC */

/** The trace output class */
class CVC4_PUBLIC TraceC {
  std::ostream* d_os;
  std::set<std::string> d_tags;

public:
  explicit TraceC(std::ostream* os) : d_os(os) {}

  CVC4ostream operator()(std::string tag) const
  {
    if(!d_tags.empty() && d_tags.find(tag) != d_tags.end()) {
      return CVC4ostream(d_os);
    } else {
      return CVC4ostream();
    }
  }

  bool on(const std::string& tag)
  {
    d_tags.insert(tag);
    return true;
  }
  bool off(const std::string& tag)
  {
    d_tags.erase(tag);
    return false;
  }
  bool off()                { d_tags.clear(); return false; }

  bool isOn(const std::string& tag) const
  {
    return d_tags.find(tag) != d_tags.end();
  }

  std::ostream& setStream(std::ostream* os) { d_os = os; return *d_os; }
  std::ostream& getStream() const { return *d_os; }
  std::ostream* getStreamPointer() const { return d_os; }

};/* class TraceC */

/** The dump output class */
class CVC4_PUBLIC DumpOutC {
  std::set<std::string> d_tags;
  std::ostream* d_os;

public:
  /**
   * A copy of cout for use by the dumper.  This is important because
   * it has different settings (e.g., the expr printing depth is always
   * unlimited). */
  static std::ostream dump_cout;

  explicit DumpOutC(std::ostream* os) : d_os(os) {}

  CVC4ostream operator()(std::string tag) {
    if(!d_tags.empty() && d_tags.find(tag) != d_tags.end()) {
      return CVC4ostream(d_os);
    } else {
      return CVC4ostream();
    }
  }

  bool on(const std::string& tag)
  {
    d_tags.insert(tag);
    return true;
  }
  bool off(const std::string& tag)
  {
    d_tags.erase(tag);
    return false;
  }
  bool off()                { d_tags.clear(); return false; }

  bool isOn(std::string tag) const { return d_tags.find(tag) != d_tags.end(); }

  std::ostream& setStream(std::ostream* os) { d_os = os; return *d_os; }
  std::ostream& getStream() const { return *d_os; }
  std::ostream* getStreamPointer() const { return d_os; }
};/* class DumpOutC */

/** The debug output singleton */
extern DebugC DebugChannel CVC4_PUBLIC;
/** The warning output singleton */
extern WarningC WarningChannel CVC4_PUBLIC;
/** The message output singleton */
extern MessageC MessageChannel CVC4_PUBLIC;
/** The notice output singleton */
extern NoticeC NoticeChannel CVC4_PUBLIC;
/** The chat output singleton */
extern ChatC ChatChannel CVC4_PUBLIC;
/** The trace output singleton */
extern TraceC TraceChannel CVC4_PUBLIC;
/** The dump output singleton */
extern DumpOutC DumpOutChannel CVC4_PUBLIC;

#ifdef CVC4_MUZZLE

#  define Debug ::CVC4::__cvc4_true() ? ::CVC4::nullCvc4Stream : ::CVC4::DebugChannel
#  define Warning ::CVC4::__cvc4_true() ? ::CVC4::nullCvc4Stream : ::CVC4::WarningChannel
#  define WarningOnce ::CVC4::__cvc4_true() ? ::CVC4::nullCvc4Stream : ::CVC4::WarningChannel
#  define Message ::CVC4::__cvc4_true() ? ::CVC4::nullCvc4Stream : ::CVC4::MessageChannel
#  define Notice ::CVC4::__cvc4_true() ? ::CVC4::nullCvc4Stream : ::CVC4::NoticeChannel
#  define Chat ::CVC4::__cvc4_true() ? ::CVC4::nullCvc4Stream : ::CVC4::ChatChannel
#  define Trace ::CVC4::__cvc4_true() ? ::CVC4::nullCvc4Stream : ::CVC4::TraceChannel
#  define DumpOut ::CVC4::__cvc4_true() ? ::CVC4::nullCvc4Stream : ::CVC4::DumpOutChannel

#else /* CVC4_MUZZLE */

#  if defined(CVC4_DEBUG) && defined(CVC4_TRACING)
#    define Debug ::CVC4::DebugChannel
#  else /* CVC4_DEBUG && CVC4_TRACING */
#    define Debug ::CVC4::__cvc4_true() ? ::CVC4::nullCvc4Stream : ::CVC4::DebugChannel
#  endif /* CVC4_DEBUG && CVC4_TRACING */
#  define Warning (! ::CVC4::WarningChannel.isOn()) ? ::CVC4::nullCvc4Stream : ::CVC4::WarningChannel
#  define WarningOnce (! ::CVC4::WarningChannel.isOn() || ! ::CVC4::WarningChannel.warnOnce(__FILE__,__LINE__)) ? ::CVC4::nullCvc4Stream : ::CVC4::WarningChannel
#  define Message (! ::CVC4::MessageChannel.isOn()) ? ::CVC4::nullCvc4Stream : ::CVC4::MessageChannel
#  define Notice (! ::CVC4::NoticeChannel.isOn()) ? ::CVC4::nullCvc4Stream : ::CVC4::NoticeChannel
#  define Chat (! ::CVC4::ChatChannel.isOn()) ? ::CVC4::nullCvc4Stream : ::CVC4::ChatChannel
#  ifdef CVC4_TRACING
#    define Trace ::CVC4::TraceChannel
#  else /* CVC4_TRACING */
#    define Trace ::CVC4::__cvc4_true() ? ::CVC4::nullCvc4Stream : ::CVC4::TraceChannel
#  endif /* CVC4_TRACING */
#  ifdef CVC4_DUMPING
#    define DumpOut ::CVC4::DumpOutChannel
#  else /* CVC4_DUMPING */
#    define DumpOut ::CVC4::__cvc4_true() ? ::CVC4::nullCvc4Stream : ::CVC4::DumpOutChannel
#  endif /* CVC4_DUMPING */

#endif /* CVC4_MUZZLE */

// Disallow e.g. !Debug("foo").isOn() forms
// because the ! will apply before the ? .
// If a compiler error has directed you here,
// just parenthesize it e.g. !(Debug("foo").isOn())
class __cvc4_true {
  void operator!() CVC4_UNUSED;
  void operator~() CVC4_UNUSED;
  void operator-() CVC4_UNUSED;
  void operator+() CVC4_UNUSED;
public:
  inline operator bool() { return true; }
};/* __cvc4_true */

#if defined(CVC4_DEBUG) && defined(CVC4_TRACING)

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

  ~ScopedDebug() {
    if(d_oldSetting) {
      Debug.on(d_tag);
    } else {
      Debug.off(d_tag);
    }
  }
};/* class ScopedDebug */

#else /* CVC4_DEBUG && CVC4_TRACING */

class CVC4_PUBLIC ScopedDebug {
public:
  ScopedDebug(std::string tag, bool newSetting = true) {}
};/* class ScopedDebug */

#endif /* CVC4_DEBUG && CVC4_TRACING */

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
};/* class ScopedTrace */

#endif /* CVC4_TRACING */

/**
 * Pushes an indentation level on construction, pop on destruction.
 * Useful for tracing recursive functions especially, but also can be
 * used for clearly separating different phases of an algorithm,
 * or iterations of a loop, or... etc.
 */
class CVC4_PUBLIC IndentedScope {
  CVC4ostream d_out;
public:
  inline IndentedScope(CVC4ostream out);
  inline ~IndentedScope();
};/* class IndentedScope */

#if defined(CVC4_DEBUG) && defined(CVC4_TRACING)
inline IndentedScope::IndentedScope(CVC4ostream out) : d_out(out) { d_out << push; }
inline IndentedScope::~IndentedScope() { d_out << pop; }
#else /* CVC4_DEBUG && CVC4_TRACING */
inline IndentedScope::IndentedScope(CVC4ostream out) {}
inline IndentedScope::~IndentedScope() {}
#endif /* CVC4_DEBUG && CVC4_TRACING */

}/* CVC4 namespace */

#endif /* __CVC4__OUTPUT_H */
