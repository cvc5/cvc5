/*********************                                                        */
/*! \file dump.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Morgan Deters, Andres Noetzli, Tim King
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Dump utility classes and functions
 **
 ** Dump utility classes and functions.
 **/

#include "cvc4_private.h"

#ifndef CVC4__DUMP_H
#define CVC4__DUMP_H

#include "base/output.h"
#include "smt/command.h"

namespace CVC4 {

#if defined(CVC4_DUMPING) && !defined(CVC4_MUZZLE)

class CVC4_PUBLIC CVC4dumpstream
{
 public:
  CVC4dumpstream() : d_os(nullptr) {}
  CVC4dumpstream(std::ostream& os) : d_os(&os) {}

  CVC4dumpstream& operator<<(const Command& c) {
    if (d_os != nullptr)
    {
      (*d_os) << c << std::endl;
    }
    return *this;
  }

 private:
  std::ostream* d_os;
}; /* class CVC4dumpstream */

#else

/**
 * Dummy implementation of the dump stream when dumping is disabled or the
 * build is muzzled.
 */
class CVC4_PUBLIC CVC4dumpstream
{
 public:
  CVC4dumpstream() {}
  CVC4dumpstream(std::ostream& os) {}
  CVC4dumpstream& operator<<(const Command& c) { return *this; }
}; /* class CVC4dumpstream */

#endif /* CVC4_DUMPING && !CVC4_MUZZLE */

/** The dump class */
class CVC4_PUBLIC DumpC
{
 public:
  CVC4dumpstream operator()(const char* tag) {
    if(!d_tags.empty() && d_tags.find(std::string(tag)) != d_tags.end()) {
      return CVC4dumpstream(getStream());
    } else {
      return CVC4dumpstream();
    }
  }

  CVC4dumpstream operator()(std::string tag) {
    if(!d_tags.empty() && d_tags.find(tag) != d_tags.end()) {
      return CVC4dumpstream(getStream());
    } else {
      return CVC4dumpstream();
    }
  }

  bool on (const char* tag) { d_tags.insert(std::string(tag)); return true; }
  bool on (std::string tag) { d_tags.insert(tag); return true; }
  bool off(const char* tag) { d_tags.erase (std::string(tag)); return false; }
  bool off(std::string tag) { d_tags.erase (tag); return false; }
  bool off()                { d_tags.clear(); return false; }

  bool isOn(const char* tag) { return d_tags.find(std::string(tag)) != d_tags.end(); }
  bool isOn(std::string tag) { return d_tags.find(tag) != d_tags.end(); }

  std::ostream& setStream(std::ostream* os);
  std::ostream& getStream();
  std::ostream* getStreamPointer();

  void setDumpFromString(const std::string& optarg);

 private:
  /** Set of dumping tags that are currently active. */
  std::set<std::string> d_tags;

  /** The message printed on `--dump help`. */
  static const std::string s_dumpHelp;
};/* class DumpC */

/** The dump singleton */
extern DumpC DumpChannel CVC4_PUBLIC;

#define Dump ::CVC4::DumpChannel

}/* CVC4 namespace */

#endif /* CVC4__DUMP_H */
