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

#include <map>
#include <memory>
#include <string>
#include <vector>

#include "context/cdhashmap_forward.h"
#include "options/options.h"
#include "smt/output_manager.h"
#include "smt/smt_mode.h"
#include "theory/logic_info.h"
#include "util/result.h"
#include "util/sexpr.h"
#include "util/statistics.h"

namespace CVC4 {

class NodeManager;
class StatisticsRegistry;
class Printer;
class ResourceManager;

/* -------------------------------------------------------------------------- */

namespace context {
  class Context;
  class UserContext;
}/* CVC4::context namespace */

/* -------------------------------------------------------------------------- */

namespace smt {
/** Utilities */
class AbstractValues;
class Assertions;
class DumpManager;

}/* CVC4::smt namespace */

/* -------------------------------------------------------------------------- */

namespace theory {
  class Rewriter;
}/* CVC4::theory namespace */


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

  /** Get the logic information currently set. */
  const LogicInfo& getLogicInfo() const;
  
  /**
   * Set a resource limit for Env operations.  This is like a time
   * limit, but it's deterministic so that reproducible results can be
   * obtained.  Currently, it's based on the number of conflicts.
   * However, please note that the definition may change between different
   * versions of CVC4 (as may the number of conflicts required, anyway),
   * and it might even be different between instances of the same version
   * of CVC4 on different platforms.
   *
   * A cumulative and non-cumulative (per-call) resource limit can be
   * set at the same time.  A call to setResourceLimit() with
   * cumulative==true replaces any cumulative resource limit currently
   * in effect; a call with cumulative==false replaces any per-call
   * resource limit currently in effect.  Time limits can be set in
   * addition to resource limits; the Env obeys both.  That means
   * that up to four independent limits can control the Env
   * at the same time.
   *
   * When an Env is first created, it has no time or resource
   * limits.
   *
   * Currently, these limits only cause the Env to stop what its
   * doing when the limit expires (or very shortly thereafter); no
   * heuristics are altered by the limits or the threat of them expiring.
   * We reserve the right to change this in the future.
   *
   * @param units the resource limit, or 0 for no limit
   * @param cumulative whether this resource limit is to be a cumulative
   * resource limit for all remaining calls into the Env (true), or
   * whether it's a per-call resource limit (false); the default is false
   */
  void setResourceLimit(unsigned long units, bool cumulative = false);

  /**
   * Set a per-call time limit for Env operations.
   *
   * A per-call time limit can be set at the same time and replaces
   * any per-call time limit currently in effect.
   * Resource limits (either per-call or cumulative) can be set in
   * addition to a time limit; the Env obeys all three of them.
   *
   * Note that the per-call timer only ticks away when one of the
   * Env's workhorse functions (things like assertFormula(),
   * checkEntailed(), checkSat(), and simplify()) are running.
   * Between calls, the timer is still.
   *
   * When an Env is first created, it has no time or resource
   * limits.
   *
   * Currently, these limits only cause the Env to stop what its
   * doing when the limit expires (or very shortly thereafter); no
   * heuristics are altered by the limits or the threat of them expiring.
   * We reserve the right to change this in the future.
   *
   * @param millis the time limit in milliseconds, or 0 for no limit
   */
  void setTimeLimit(unsigned long millis);

  /**
   * Get the current resource usage count for this Env.  This
   * function can be used to ascertain reasonable values to pass as
   * resource limits to setResourceLimit().
   */
  unsigned long getResourceUsage() const;

  /** Get the current millisecond count for this Env.  */
  unsigned long getTimeUsage() const;

  /**
   * Get the remaining resources that can be consumed by this Env
   * according to the currently-set cumulative resource limit.  If there
   * is not a cumulative resource limit set, this function throws a
   * ModalException.
   *
   * @throw ModalException
   */
  unsigned long getResourceRemaining() const;

  /** Permit access to the underlying NodeManager. */
  NodeManager* getNodeManager() const;

  /** Export statistics from this Env. */
  Statistics getStatistics() const;

  /** Get the value of one named statistic from this Env. */
  SExpr getStatistic(std::string name) const;

  /** Flush statistics from this Env and the NodeManager it uses. */
  void flushStatistics(std::ostream& out) const;

  /**
   * Flush statistics from this Env and the NodeManager it uses. Safe to
   * use in a signal handler.
   */
  void safeFlushStatistics(int fd) const;

  /** Get the options object (const version only) */
  const Options& getOptions() const;

  /** Get a pointer to the UserContext owned by this Env. */
  context::UserContext* getUserContext();

  /** Get a pointer to the Context owned by this Env. */
  context::Context* getContext();

  /** Permit access to the underlying dump manager. */
  smt::DumpManager* getDumpManager();

  /** Get the resource manager of this SMT engine */
  ResourceManager* getResourceManager();

  /** Get the printer used by this SMT engine */
  const Printer* getPrinter() const;

  /** Get the output manager for this SMT engine */
  OutputManager& getOutputManager();

  /** Get a pointer to the Rewriter owned by this Env. */
  theory::Rewriter* getRewriter() { return d_rewriter.get(); }

 private:

  /** Get a pointer to the StatisticsRegistry owned by this Env. */
  StatisticsRegistry* getStatisticsRegistry()
  {
    return d_statisticsRegistry.get();
  };

  /* Members -------------------------------------------------------------- */

  /** Expr manager context */
  std::unique_ptr<context::Context> d_context;
  /** User level context */
  std::unique_ptr<context::UserContext> d_userContext;
  /** Our internal node manager */
  NodeManager* d_nodeManager;
  /** The proof node manager */
  ProofNodeManager * d_pnm;
  /** The dump manager */
  std::unique_ptr<smt::DumpManager> d_dumpm;
  /**
   * The rewriter associated with this Env. We have a different instance
   * of the rewriter for each Env instance. This is because rewriters may
   * hold references to objects that belong to theory solvers, which are
   * specific to an Env/TheoryEngine instance.
   */
  std::unique_ptr<theory::Rewriter> d_rewriter;
  /**
   * The logic we're in. This logic may be an extension of the logic set by the
   * user.
   */
  LogicInfo d_logic;
  /** The statistics registry */
  std::unique_ptr<StatisticsRegistry> d_statisticsRegistry;
  /** The options object */
  Options d_options;
  /** the output manager for commands */
  mutable OutputManager d_outMgr;
  /**
   * Manager for limiting time and abstract resource usage.
   */
  std::unique_ptr<ResourceManager> d_resourceManager;
}; /* class Env */

/* -------------------------------------------------------------------------- */

}/* CVC4 namespace */

#endif /* CVC4__SMT__ENV_H */
