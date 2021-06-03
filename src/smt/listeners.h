/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Abdalrhman Mohamed, Mathias Preiner
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Listener classes for SMT engine.
 */

#include "cvc5_private.h"

#ifndef CVC5__SMT__LISTENERS_H
#define CVC5__SMT__LISTENERS_H

#include <vector>

#include "base/listener.h"
#include "expr/node.h"

namespace cvc5 {

class OutputManager;
class SmtEngine;

namespace smt {

/** A listener for resource outs */
class ResourceOutListener : public Listener
{
 public:
  ResourceOutListener(SmtEngine& smt);
  /** notify method, interupts SmtEngine */
  void notify() override;

 private:
  /** Reference to the SmtEngine */
  SmtEngine& d_smt;
};

class DumpManager;

/**
 * A listener for node manager calls, which impacts certain dumping traces.
 */
class SmtNodeManagerListener : public NodeManagerListener
{
 public:
  SmtNodeManagerListener(DumpManager& dm, OutputManager& outMgr);
  /** Notify when new sort is created */
  void nmNotifyNewSort(TypeNode tn, uint32_t flags) override;
  /** Notify when new sort constructor is created */
  void nmNotifyNewSortConstructor(TypeNode tn, uint32_t flags) override;
  /** Notify when list of datatypes is created */
  void nmNotifyNewDatatypes(const std::vector<TypeNode>& dtts,
                            uint32_t flags) override;
  /** Notify when new variable is created */
  void nmNotifyNewVar(TNode n) override;
  /** Notify when new skolem is created */
  void nmNotifyNewSkolem(TNode n,
                         const std::string& comment,
                         uint32_t flags) override;
  /** Notify when a term is deleted */
  void nmNotifyDeleteNode(TNode n) override {}

 private:
  /** Reference to the dump manager of smt engine */
  DumpManager& d_dm;
  /** Reference to the output manager of the smt engine */
  OutputManager& d_outMgr;
};

}  // namespace smt
}  // namespace cvc5

#endif
