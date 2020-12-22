/*********************                                                        */
/*! \file unsat_core_manager.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Haniel Barbosa
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief The unsat core manager of SmtEngine.
 **/

#include "cvc4_private.h"

#ifndef CVC4__SMT__UNSAT_CORE_MANAGER_H
#define CVC4__SMT__UNSAT_CORE_MANAGER_H

#include "context/cdhashmap.h"
#include "context/cdlist.h"
#include "expr/node.h"
#include "expr/proof_node.h"

namespace CVC4 {

namespace smt {

class Assertions;

/**
 * This class is responsible for managing the proof output of SmtEngine, as
 * well as setting up the global proof checker and proof node manager.
 */
class UnsatCoreManager
{
 public:
  UnsatCoreManager() {}
  ~UnsatCoreManager(){};

  /** Gets the unsat core.
   *
   * The unsat core is the intersection of the assertions in as and the free
   * assumptions of the underlying refutation proof of pfn. Note that pfn must
   * be a "final proof", which means that it's a proof of false under a scope
   * containing all assertions.
   *
   * The unsat core is stored in the core argument.
   */
  void getUnsatCore(std::shared_ptr<ProofNode> pfn,
                    Assertions& as,
                    std::vector<Node>& core);

  /** Gets the relevant instaniations for the refutation.
   *
   * The relevant instantiations are all the conclusions of proof nodes of type
   * INSTANTIATE that occur in pfn.
   *
   * This method populates the insts map from quantified formulas occurring as
   * premises of INSTANTIATE proof nodes to its instantiations, which are a
   * matrix with each row corresponding to the terms with which the respective
   * quantified formula is instiated.
   */
  void getRelevantInstantiations(
      std::shared_ptr<ProofNode> pfn,
      std::map<Node, std::vector<std::vector<Node>>>& insts);

}; /* class UnsatCoreManager */

}  // namespace smt
}  // namespace CVC4

#endif /* CVC4__SMT__UNSAT_CORE_MANAGER_H */
