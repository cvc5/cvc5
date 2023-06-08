/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Aina Niemetz, Tim King
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * First order model for full model check.
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__QUANTIFIERS__FMF__FIRST_ORDER_MODEL_FMC_H
#define CVC5__THEORY__QUANTIFIERS__FMF__FIRST_ORDER_MODEL_FMC_H

#include "theory/quantifiers/first_order_model.h"

namespace cvc5::internal {
namespace theory {
namespace quantifiers {
namespace fmcheck {

class Def;

class FirstOrderModelFmc : public FirstOrderModel
{
  friend class FullModelChecker;

 private:
  /** models for UF */
  std::map<Node, Def*> d_models;
  std::map<TypeNode, Node> d_type_star;
  /** get current model value */
  void processInitializeModelForTerm(Node n) override;

 public:
  FirstOrderModelFmc(Env& env,
                     QuantifiersState& qs,
                     QuantifiersRegistry& qr,
                     TermRegistry& tr);
  ~FirstOrderModelFmc() override;
  // initialize the model
  void processInitialize(bool ispre) override;
  Node getFunctionValue(Node op, const char* argPrefix);

  static bool isStar(Node n);
  Node getStar(TypeNode tn);
}; /* class FirstOrderModelFmc */

}  // namespace fmcheck
}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5__FIRST_ORDER_MODEL_H */
