/*********************                                                        */
/*! \file sygus_solver.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief The solver for sygus queries
 **/

#include "cvc4_private.h"

#ifndef CVC4__SMT__SYGUS_SOLVER_H
#define CVC4__SMT__SYGUS_SOLVER_H

#include "expr/node.h"
#include "expr/type_node.h"

namespace CVC4 {

class SmtEngine;

namespace smt {

/**
 * A solver for sygus queries.
 *
 * This class is responsible for responding to check-synth commands. It calls
 * check satisfiability.
 */
class SygusSolver
{
 public:
  SygusSolver(SmtEngine& smt);
  ~SygusSolver();

 private:
  /** The parent SMT engine */
  SmtEngine& d_smt;
  /**
   * sygus variables declared (from "declare-var" and "declare-fun" commands)
   *
   * The SyGuS semantics for declared variables is that they are implicitly
   * universally quantified in the constraints.
   */
  std::vector<Node> d_sygusVars;
  /** sygus constraints */
  std::vector<Node> d_sygusConstraints;
  /** functions-to-synthesize */
  std::vector<Node> d_sygusFunSymbols;
  /**
   * Whether we need to reconstruct the sygus conjecture.
   */
  CDO<bool> d_sygusConjectureStale;
};

}  // namespace smt
}  // namespace CVC4

#endif /* CVC4__SMT__SYGUS_SOLVER_H */
