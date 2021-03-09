/*********************                                                        */
/*! \file env.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Morgan Deters, Aina Niemetz
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Smt Environment, main access to global utilities available to
 ** internal code
 **/

#include "cvc4_public.h"

#ifndef CVC4__SMT__ENV_H
#define CVC4__SMT__ENV_H

#include "context/context.h"
#include "options/options.h"
#include "smt/output_manager.h"
#include "theory/logic_info.h"
#include "util/result.h"
#include "util/sexpr.h"
#include "util/statistics.h"

namespace CVC4 {

class NodeManager;
class StatisticsRegistry;
class ProofNodeManager;
class Printer;
class ResourceManager;

/* -------------------------------------------------------------------------- */

namespace context {
class Context;
class UserContext;
}  // namespace context

/* -------------------------------------------------------------------------- */

namespace smt {
/** Utilities */
class DumpManager;
}  // namespace smt

/* -------------------------------------------------------------------------- */

namespace theory {
class Rewriter;
}  // namespace theory

/* -------------------------------------------------------------------------- */

class Env
{
  friend class SmtEngine;
  /* .......................................................................  */
 public:
  /* .......................................................................  */

  /**
   * Construct an Env with the given node manager. If provided, optr is a
   * pointer to a set of options that should initialize the values of the
   * options object owned by this class.
   */
  Env(NodeManager* nm, Options* optr = nullptr);
  /** Destruct the env.  */
  ~Env();
  
  /** Get a pointer to the Context owned by this Env. */
  context::Context* getContext();
  
  /** Get a pointer to the UserContext owned by this Env. */
  context::UserContext* getUserContext();
  
  /** Permit access to the underlying NodeManager. */
  NodeManager* getNodeManager() const;
  
  /** Get the underlying proof node manager */
  ProofNodeManager* getProofNodeManager();

  /** Get a pointer to the Rewriter owned by this Env. */
  theory::Rewriter* getRewriter();

  /** Permit access to the underlying dump manager. */
  smt::DumpManager* getDumpManager();

  /** Get the options object (const version only) */
  const Options& getOptions() const;
  
  /** Get the resource manager of this SMT engine */
  ResourceManager* getResourceManager();

  /** Get the logic information currently set. */
  const LogicInfo& getLogicInfo() const;

  /** Get a pointer to the StatisticsRegistry owned by this Env. */
  StatisticsRegistry* getStatisticsRegistry();
  
  
  /* Option helpers -------------------------------------------------------------- */

  /** Get the current printer based on the current options
   *
   * @return the current printer
   */
  const Printer& getPrinter();

  /** Get the output stream that --dump=X should print to
   *
   * @return the output stream
   */
  std::ostream& getDumpOut();
  
 private:

  /* Members -------------------------------------------------------------- */

  /** Expr manager context */
  std::unique_ptr<context::Context> d_context;
  /** User level context */
  std::unique_ptr<context::UserContext> d_userContext;
  /** Our internal node manager */
  NodeManager* d_nodeManager;
  /** The proof node manager */
  ProofNodeManager* d_pnm;
  /**
   * The rewriter associated with this Env. We have a different instance
   * of the rewriter for each Env instance. This is because rewriters may
   * hold references to objects that belong to theory solvers, which are
   * specific to an Env/TheoryEngine instance.
   */
  std::unique_ptr<theory::Rewriter> d_rewriter;
  /** The dump manager */
  std::unique_ptr<smt::DumpManager> d_dumpm;
  /**
   * The logic we're in. This logic may be an extension of the logic set by the
   * user.
   */
  LogicInfo d_logic;
  /** The statistics registry */
  std::unique_ptr<StatisticsRegistry> d_statisticsRegistry;
  /** The options object */
  Options d_options;
  /**
   * Manager for limiting time and abstract resource usage.
   */
  std::unique_ptr<ResourceManager> d_resourceManager;
}; /* class Env */

/* -------------------------------------------------------------------------- */

}  // namespace CVC4

#endif /* CVC4__SMT__ENV_H */
