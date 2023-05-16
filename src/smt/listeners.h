/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Aina Niemetz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
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

namespace cvc5::internal {

class SolverEngine;

namespace smt {

/** A listener for resource outs */
class ResourceOutListener : public Listener
{
 public:
  ResourceOutListener(SolverEngine& smt);
  /** notify method, interupts SolverEngine */
  void notify() override;

 private:
  /** Reference to the SolverEngine */
  SolverEngine& d_slv;
};

}  // namespace smt
}  // namespace cvc5::internal

#endif
