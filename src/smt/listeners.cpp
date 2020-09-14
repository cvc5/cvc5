/*********************                                                        */
/*! \file listeners.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Implements listener classes for SMT engine.
 **/

#include "smt/listeners.h"

#include "expr/attribute.h"
#include "expr/expr.h"
#include "expr/node_manager_attributes.h"
#include "options/smt_options.h"
#include "smt/node_command.h"
#include "smt/dump.h"
#include "smt/dump_manager.h"
#include "smt/smt_engine.h"
#include "smt/smt_engine_scope.h"

namespace CVC4 {
namespace smt {

ResourceOutListener::ResourceOutListener(SmtEngine& smt) : d_smt(smt) {}

void ResourceOutListener::notify()
{
  SmtScope scope(&d_smt);
  Assert(smt::smtEngineInScope());
  d_smt.interrupt();
}

SmtNodeManagerListener::SmtNodeManagerListener(DumpManager& dm) : d_dm(dm) {}

void SmtNodeManagerListener::nmNotifyNewSort(TypeNode tn, uint32_t flags)
{
  DeclareTypeNodeCommand c(tn.getAttribute(expr::VarNameAttr()), 0, tn);
  if ((flags & ExprManager::SORT_FLAG_PLACEHOLDER) == 0)
  {
    d_dm.addToModelCommandAndDump(c, flags);
  }
}

void SmtNodeManagerListener::nmNotifyNewSortConstructor(TypeNode tn,
                                                        uint32_t flags)
{
  DeclareTypeNodeCommand c(tn.getAttribute(expr::VarNameAttr()),
                           tn.getAttribute(expr::SortArityAttr()),
                           tn);
  if ((flags & ExprManager::SORT_FLAG_PLACEHOLDER) == 0)
  {
    d_dm.addToModelCommandAndDump(c);
  }
}

void SmtNodeManagerListener::nmNotifyNewDatatypes(
    const std::vector<TypeNode>& dtts, uint32_t flags)
{
  if ((flags & NodeManager::DATATYPE_FLAG_PLACEHOLDER) == 0)
  {
    std::vector<Type> types;
    for (const TypeNode& dt : dtts)
    {
      Assert(dt.isDatatype());
    }
    DeclareDatatypeNodeCommand c(dtts);
    d_dm.addToModelCommandAndDump(c);
  }
}

void SmtNodeManagerListener::nmNotifyNewVar(TNode n, uint32_t flags)
{
  DeclareFunctionNodeCommand c(
      n.getAttribute(expr::VarNameAttr()), n, n.getType());
  if ((flags & ExprManager::VAR_FLAG_DEFINED) == 0)
  {
    d_dm.addToModelCommandAndDump(c, flags);
  }
}

void SmtNodeManagerListener::nmNotifyNewSkolem(TNode n,
                                               const std::string& comment,
                                               uint32_t flags)
{
  std::string id = n.getAttribute(expr::VarNameAttr());
  DeclareFunctionNodeCommand c(id, n, n.getType());
  if (Dump.isOn("skolems") && comment != "")
  {
    Dump("skolems") << CommentCommand(id + " is " + comment);
  }
  if ((flags & ExprManager::VAR_FLAG_DEFINED) == 0)
  {
    d_dm.addToModelCommandAndDump(c, flags, false, "skolems");
  }
}

}  // namespace smt
}  // namespace CVC4
