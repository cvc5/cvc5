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

#include "expr/expr_manager.h"
#include "options/smt_options.h"
#include "smt/dump.h"

namespace CVC4 {
namespace smt {

DumpManager::DumpManager(context::UserContext* u)
    : d_fullyInited(false),
      d_modelGlobalCommands(),
      d_modelCommands(u),
      d_dumpCommands()
{
}

DumpManager::~DumpManager()
{
  d_dumpCommands.clear();
  d_modelCommandsAlloc.clear();
  d_modelGlobalCommands.clear();
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

void DumpManager::resetAssertions() { d_modelGlobalCommands.clear(); }

void DumpManager::addToModelCommandAndDump(const NodeCommand& c,
                                           uint32_t flags,
                                           bool userVisible,
                                           const char* dumpTag)
{
  Trace("smt") << "SMT addToModelCommandAndDump(" << c << ")" << std::endl;
  // If we aren't yet fully inited, the user might still turn on
  // produce-models.  So let's keep any commands around just in
  // case.  This is useful in two cases: (1) SMT-LIBv1 auto-declares
  // sort "U" in QF_UF before setLogic() is run and we still want to
  // support finding card(U) with --finite-model-find, and (2) to
  // decouple SmtEngine and ExprManager if the user does a few
  // ExprManager::mkSort() before SmtEngine::setOption("produce-models")
  // and expects to find their cardinalities in the model.
  if ((!d_fullyInited || options::produceModels())
      && (flags & ExprManager::VAR_FLAG_DEFINED) == 0)
  {
    if (flags & ExprManager::VAR_FLAG_GLOBAL)
    {
      d_modelGlobalCommands.push_back(std::unique_ptr<NodeCommand>(c.clone()));
    }
    else
    {
      NodeCommand* cc = c.clone();
      d_modelCommands.push_back(cc);
      // also remember for memory management purposes
      d_modelCommandsAlloc.push_back(std::unique_ptr<NodeCommand>(cc));
    }
  }
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
  for (std::unique_ptr<NodeCommand>& c : d_modelGlobalCommands)
  {
    DeclareFunctionCommand* dfc =
        dynamic_cast<DeclareFunctionCommand*>(c.get());
    if (dfc != NULL)
    {
      Node df = Node::fromExpr(dfc->getFunction());
      if (df == f)
      {
        dfc->setPrintInModel(p);
      }
    }
  }
  for (NodeCommand* c : d_modelCommands)
  {
    DeclareFunctionCommand* dfc = dynamic_cast<DeclareFunctionCommand*>(c);
    if (dfc != NULL)
    {
      Node df = Node::fromExpr(dfc->getFunction());
      if (df == f)
      {
        dfc->setPrintInModel(p);
      }
    }
  }
}

size_t DumpManager::getNumModelCommands() const
{
  return d_modelCommands.size() + d_modelGlobalCommands.size();
}

const NodeCommand* DumpManager::getModelCommand(size_t i) const
{
  Assert(i < getNumModelCommands());
  // index the global commands first, then the locals
  if (i < d_modelGlobalCommands.size())
  {
    return d_modelGlobalCommands[i].get();
  }
  return d_modelCommands[i - d_modelGlobalCommands.size()];
}

}  // namespace smt
}  // namespace CVC4
