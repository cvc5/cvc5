/*********************                                                        */
/*! \file dump_manager.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Implementation of the dump manager.
 **/

#include "smt/dump_manager.h"

#include "options/smt_options.h"

namespace CVC4 {
namespace smt {

struct DeleteCommandFunction : public std::unary_function<const Command*, void>
{
  void operator()(const Command* command) { delete command; }
};

void DeleteAndClearCommandVector(std::vector<Command*>& commands) {
  std::for_each(commands.begin(), commands.end(), DeleteCommandFunction());
  commands.clear();
}
  
DumpManager::DumpManager(context::UserContext* u) 
    : d_modelGlobalCommands(),
      d_modelCommands(nullptr),
      d_dumpCommands(),
{
  d_modelCommands = new (true) smt::CommandList(u);
}

DumpManager::~DumpManager() {
  for(size_t i = 0, ncoms = d_dumpCommands.size(); i < ncoms; ++i) {
    delete d_dumpCommands[i];
    d_dumpCommands[i] = nullptr;
  }
  d_dumpCommands.clear();

  DeleteAndClearCommandVector(d_modelGlobalCommands);

  if(d_modelCommands != nullptr) {
    d_modelCommands->deleteSelf();
  }
}

void DumpManager::finishInit()
{
  Trace("smt-debug") << "Dump declaration commands..." << std::endl;
  // dump out any pending declaration commands
  for(size_t i = 0, ncoms = d_dumpCommands.size(); i < ncoms; ++i) {
    Dump("declarations") << *d_dumpCommands[i];
    delete d_dumpCommands[i];
  }
  d_dumpCommands.clear();
  
  d_fullyInited = true;
}

void DumpManager::resetAssertions()
{
  
}

void DumpManager::addToModelCommandAndDump(const Command& c, uint32_t flags, const char* dumpTag) {
  Trace("smt") << "SMT addToModelCommandAndDump(" << c << ")" << endl;
  // If we aren't yet fully inited, the user might still turn on
  // produce-models.  So let's keep any commands around just in
  // case.  This is useful in two cases: (1) SMT-LIBv1 auto-declares
  // sort "U" in QF_UF before setLogic() is run and we still want to
  // support finding card(U) with --finite-model-find, and (2) to
  // decouple SmtEngine and ExprManager if the user does a few
  // ExprManager::mkSort() before SmtEngine::setOption("produce-models")
  // and expects to find their cardinalities in the model.
  if((!d_fullyInited || options::produceModels()) &&
     (flags & ExprManager::VAR_FLAG_DEFINED) == 0) {
    if(flags & ExprManager::VAR_FLAG_GLOBAL) {
      d_modelGlobalCommands.push_back(c.clone());
    } else {
      d_modelCommands->push_back(c.clone());
    }
  }
  if(Dump.isOn(dumpTag)) {
    if(d_fullyInited) {
      Dump(dumpTag) << c;
    } else {
      d_dumpCommands.push_back(c.clone());
    }
  }
}

}  // namespace smt
}  // namespace CVC4
