/*********************                                                        */
/*! \file dump_manager.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Gereon Kremer, Abdalrhman Mohamed
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Implementation of the dump manager.
 **/

#include "smt/dump_manager.h"

#include "options/smt_options.h"
#include "smt/dump.h"
#include "smt/node_command.h"

namespace CVC4 {
namespace smt {

DumpManager::DumpManager(context::UserContext* u)
    : d_fullyInited(false),
      d_dumpCommands()
{
}

DumpManager::~DumpManager()
{
  d_dumpCommands.clear();
}

void DumpManager::finishInit()
{
  Trace("smt-debug") << "Dump declaration commands..." << std::endl;
  // dump out any pending declaration commands
  for (size_t i = 0, ncoms = d_dumpCommands.size(); i < ncoms; ++i)
  {
    Dump("declarations") << *d_dumpCommands[i];
  }
  d_dumpCommands.clear();

  d_fullyInited = true;
}
void DumpManager::resetAssertions()
{
  // currently, do nothing
}

void DumpManager::addToDump(const NodeCommand& c, const char* dumpTag)
{
  Trace("smt") << "SMT addToDump(" << c << ")" << std::endl;
  if (Dump.isOn(dumpTag))
  {
    if (d_fullyInited)
    {
      Dump(dumpTag) << c;
    }
    else
    {
      d_dumpCommands.push_back(std::unique_ptr<NodeCommand>(c.clone()));
    }
  }
}

void DumpManager::setPrintFuncInModel(Node f, bool p)
{
  Trace("setp-model") << "Set printInModel " << f << " to " << p << std::endl;
  // TODO (cvc4-wishues/issues/75): implement
}

}  // namespace smt
}  // namespace CVC4
