/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Abdalrhman Mohamed
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Implements listener classes for SMT engine.
 */

#include "smt/listeners.h"

#include "base/configuration.h"
#include "expr/attribute.h"
#include "expr/node_manager_attributes.h"
#include "options/smt_options.h"
#include "printer/printer.h"
#include "smt/dump.h"
#include "smt/dump_manager.h"
#include "smt/node_command.h"
#include "smt/smt_engine.h"
#include "smt/smt_engine_scope.h"

namespace cvc5 {
namespace smt {

ResourceOutListener::ResourceOutListener(SmtEngine& smt) : d_smt(smt) {}

void ResourceOutListener::notify()
{
  SmtScope scope(&d_smt);
  Assert(smt::smtEngineInScope());
  d_smt.interrupt();
}

SmtNodeManagerListener::SmtNodeManagerListener(DumpManager& dm,
                                               OutputManager& outMgr)
    : d_dm(dm), d_outMgr(outMgr)
{
}

void SmtNodeManagerListener::nmNotifyNewSort(TypeNode tn, uint32_t flags)
{
  DeclareTypeNodeCommand c(tn.getAttribute(expr::VarNameAttr()), 0, tn);
  if ((flags & NodeManager::SORT_FLAG_PLACEHOLDER) == 0)
  {
    d_dm.addToDump(c);
  }
}

void SmtNodeManagerListener::nmNotifyNewSortConstructor(TypeNode tn,
                                                        uint32_t flags)
{
  DeclareTypeNodeCommand c(tn.getAttribute(expr::VarNameAttr()),
                           tn.getAttribute(expr::SortArityAttr()),
                           tn);
  if ((flags & NodeManager::SORT_FLAG_PLACEHOLDER) == 0)
  {
    d_dm.addToDump(c);
  }
}

void SmtNodeManagerListener::nmNotifyNewDatatypes(
    const std::vector<TypeNode>& dtts, uint32_t flags)
{
  if ((flags & NodeManager::DATATYPE_FLAG_PLACEHOLDER) == 0)
  {
    if (Configuration::isAssertionBuild())
    {
      for (CVC5_UNUSED const TypeNode& dt : dtts)
      {
        Assert(dt.isDatatype());
      }
    }
    DeclareDatatypeNodeCommand c(dtts);
    d_dm.addToDump(c);
  }
}

void SmtNodeManagerListener::nmNotifyNewVar(TNode n)
{
  DeclareFunctionNodeCommand c(
      n.getAttribute(expr::VarNameAttr()), n, n.getType());
  d_dm.addToDump(c);
}

void SmtNodeManagerListener::nmNotifyNewSkolem(TNode n,
                                               const std::string& comment,
                                               uint32_t flags)
{
  std::string id = n.getAttribute(expr::VarNameAttr());
  DeclareFunctionNodeCommand c(id, n, n.getType());
  if (Dump.isOn("skolems") && comment != "")
  {
    d_outMgr.getPrinter().toStreamCmdComment(d_outMgr.getDumpOut(),
                                             id + " is " + comment);
  }
  d_dm.addToDump(c, "skolems");
}

}  // namespace smt
}  // namespace cvc5
