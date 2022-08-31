/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2022 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Solver for arithmetic/bitvector conversions constraints.
 */

#ifndef CVC5__THEORY__UF__CONVERSIONS_SOLVER_H
#define CVC5__THEORY__UF__CONVERSIONS_SOLVER_H

#include <map>
#include <vector>

#include "context/cdhashset.h"
#include "context/cdlist.h"
#include "expr/node.h"
#include "smt/env_obj.h"

namespace cvc5::internal {
namespace theory {
  
class TheoryState;
class TheoryInferenceManager;

namespace uf {

/**
 * Arith-bitvector conversions solver
 */
class ConversionsSolver : protected EnvObj
{
  using NodeList = context::CDList<Node>;
  using NodeSet = context::CDHashSet<Node>;

 public:
  ConversionsSolver(Env& env,
                      TheoryState& state,
                      TheoryInferenceManager& im);
  ~ConversionsSolver();
  /** Preregister term */
  void preRegisterTerm(TNode term);
  /** check */
  void check();
 private:
  /** Reference to the state object */
  TheoryState& d_state;
  /** Reference to the inference manager */
  TheoryInferenceManager& d_im;
  /** Conversion terms that have been registered */
  NodeList d_preRegistered;
  /** Conversion terms that have been given reduction lemmas */
  NodeSet d_reduced;
  /** Check whether the BV conversion term n should be reduced */
  void checkReduction(Node n);
}; /* class ConversionsSolver */

}  // namespace uf
}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5__THEORY__UF__CONVERSIONS_SOLVER_H */
