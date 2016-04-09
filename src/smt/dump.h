/*********************                                                        */
/*! \file dump.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Morgan Deters, Tim King
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2016 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Dump utility classes and functions
 **
 ** Dump utility classes and functions.
 **/

#include "cvc4_private.h"

#ifndef __CVC4__DUMP_H
#define __CVC4__DUMP_H

#include "base/output.h"
#include "smt/command.h"

namespace CVC4 {

class CVC4_PUBLIC CVC4dumpstream {

#if defined(CVC4_DUMPING) && !defined(CVC4_MUZZLE)
  std::ostream* d_os;
#endif /* CVC4_DUMPING && !CVC4_MUZZLE */

#ifdef CVC4_PORTFOLIO
  CommandSequence* d_commands;
#endif /* CVC4_PORTFOLIO */

public:
  CVC4dumpstream() throw()
#if defined(CVC4_DUMPING) && !defined(CVC4_MUZZLE) && defined(CVC4_PORTFOLIO)
    : d_os(NULL), d_commands(NULL)
#elif defined(CVC4_DUMPING) && !defined(CVC4_MUZZLE)
    : d_os(NULL)
#elif defined(CVC4_PORTFOLIO)
    : d_commands(NULL)
#endif /* CVC4_PORTFOLIO */
  { }

  CVC4dumpstream(std::ostream& os, CommandSequence& commands) throw()
#if defined(CVC4_DUMPING) && !defined(CVC4_MUZZLE) && defined(CVC4_PORTFOLIO)
    : d_os(&os), d_commands(&commands)
#elif defined(CVC4_DUMPING) && !defined(CVC4_MUZZLE)
    : d_os(&os)
#elif defined(CVC4_PORTFOLIO)
    : d_commands(&commands)
#endif /* CVC4_PORTFOLIO */
  { }

  CVC4dumpstream& operator<<(const Command& c) {
#if defined(CVC4_DUMPING) && !defined(CVC4_MUZZLE)
    if(d_os != NULL) {
      (*d_os) << c << std::endl;
    }
#endif
#if defined(CVC4_PORTFOLIO)
    if(d_commands != NULL) {
      d_commands->addCommand(c.clone());
    }
#endif
    return *this;
  }
};/* class CVC4dumpstream */

/** The dump class */
class CVC4_PUBLIC DumpC {
  std::set<std::string> d_tags;
  CommandSequence d_commands;

  static const std::string s_dumpHelp;

public:
  CVC4dumpstream operator()(const char* tag) {
    if(!d_tags.empty() && d_tags.find(std::string(tag)) != d_tags.end()) {
      return CVC4dumpstream(getStream(), d_commands);
    } else {
      return CVC4dumpstream();
    }
  }

  CVC4dumpstream operator()(std::string tag) {
    if(!d_tags.empty() && d_tags.find(tag) != d_tags.end()) {
      return CVC4dumpstream(getStream(), d_commands);
    } else {
      return CVC4dumpstream();
    }
  }

  void clear() { d_commands.clear(); }
  const CommandSequence& getCommands() const { return d_commands; }

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
};/* class DumpC */

/** The dump singleton */
extern DumpC DumpChannel CVC4_PUBLIC;

#define Dump ::CVC4::DumpChannel

}/* CVC4 namespace */

#endif /* __CVC4__DUMP_H */
