/******************************************************************************
 * Top contributors (to current version):
 *   Aina Niemetz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * The base class for everything that nees access to the environment (Env)
 * instance, which gives access to global utilities available to internal code.
 */

#include "cvc5_private.h"

#ifndef CVC5__SMT__ENV_OBJ_H
#define CVC5__SMT__ENV_OBJ_H

#include <memory>

#include "expr/node.h"

namespace cvc5 {

class Env;
class NodeManager;
class Options;

class EnvObj
{
 public:
  /** Constructor. */
  EnvObj(Env& env);
  EnvObj() = delete;
  /** Destructor.  */
  ~EnvObj() {}

  /**
   * Rewrite a node.
   * This is a wrapper around theory::Rewriter::rewrite via Env.
   */
  Node rewrite(TNode node);

  /**
   * Garbage collect the rewrite caches.
   * This is a wrapper around theory::Rewriter::clearCaches via Env.
   */
  void clearRewriterCaches();

 private:
 protected:
  /** The associated environment. */
  Env& d_env;
};

}  // namespace cvc5
#endif
