/******************************************************************************
 * Top contributors (to current version):
 *   Morgan Deters, Andres Noetzli, Abdalrhman Mohamed
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Dump utility classes and functions.
 */

#include "cvc5_private.h"

#ifndef CVC5__DUMP_H
#define CVC5__DUMP_H

#include "base/output.h"

namespace cvc5 {

class Command;
class NodeCommand;

#if defined(CVC5_DUMPING) && !defined(CVC5_MUZZLE)

class CVC5dumpstream
{
 public:
  CVC5dumpstream() : d_os(nullptr) {}
  CVC5dumpstream(std::ostream& os) : d_os(&os) {}

  CVC5dumpstream& operator<<(const Command& c);

  /** A convenience function for dumping internal commands.
   *
   * Since Commands are now part of the public API, internal code should use
   * NodeCommands and this function (instead of the one above) to dump them.
   */
  CVC5dumpstream& operator<<(const NodeCommand& nc);

 private:
  std::ostream* d_os;
}; /* class CVC5dumpstream */

#else

/**
 * Dummy implementation of the dump stream when dumping is disabled or the
 * build is muzzled.
 */
class CVC5dumpstream
{
 public:
  CVC5dumpstream() {}
  CVC5dumpstream(std::ostream& os) {}
  CVC5dumpstream& operator<<(const Command& c);
  CVC5dumpstream& operator<<(const NodeCommand& nc);
}; /* class CVC5dumpstream */

#endif /* CVC5_DUMPING && !CVC5_MUZZLE */

/** The dump class */
class DumpC
{
 public:
  CVC5dumpstream operator()(const char* tag)
  {
    if(!d_tags.empty() && d_tags.find(std::string(tag)) != d_tags.end()) {
      return CVC5dumpstream(getStream());
    } else {
      return CVC5dumpstream();
    }
  }

  CVC5dumpstream operator()(std::string tag)
  {
    if(!d_tags.empty() && d_tags.find(tag) != d_tags.end()) {
      return CVC5dumpstream(getStream());
    } else {
      return CVC5dumpstream();
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
extern DumpC DumpChannel;

#define Dump ::cvc5::DumpChannel

}  // namespace cvc5

#endif /* CVC5__DUMP_H */
