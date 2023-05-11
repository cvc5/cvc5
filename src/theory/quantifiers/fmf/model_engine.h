/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Morgan Deters, Mathias Preiner
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Model Engine class.
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__QUANTIFIERS__MODEL_ENGINE_H
#define CVC5__THEORY__QUANTIFIERS__MODEL_ENGINE_H

#include "smt/env_obj.h"
#include "theory/quantifiers/fmf/model_builder.h"
#include "theory/quantifiers/quant_module.h"
#include "theory/theory_model.h"

namespace cvc5::internal {
namespace theory {
namespace quantifiers {

class ModelEngine : public QuantifiersModule
{
  friend class RepSetIterator;
private:
  //check model
  int checkModel();
  //exhaustively instantiate quantifier (possibly using mbqi)
  void exhaustiveInstantiate( Node f, int effort = 0 );
private:
  //temporary statistics
  //is the exhaustive instantiation incomplete?
  bool d_incomplete_check;
  int d_addedLemmas;
  int d_triedLemmas;
  int d_totalLemmas;
public:
 ModelEngine(Env& env,
             QuantifiersState& qs,
             QuantifiersInferenceManager& qim,
             QuantifiersRegistry& qr,
             TermRegistry& tr,
             QModelBuilder* builder);
 virtual ~ModelEngine();

public:
 bool needsCheck(Theory::Effort e) override;
 QEffort needsModel(Theory::Effort e) override;
 void reset_round(Theory::Effort e) override;
 void check(Theory::Effort e, QEffort quant_e) override;
 bool checkComplete(IncompleteId& incId) override;
 bool checkCompleteFor(Node q) override;
 void registerQuantifier(Node f) override;
 Node explain(TNode n) { return Node::null(); }
 void debugPrint(const char* c);
 /** Identify this module */
 std::string identify() const override;

private:
 /** Should we process quantified formula q? */
 bool shouldProcess(Node q);
 /** Pointer to the model builder of quantifiers engine */
 QModelBuilder* d_builder;
 /** set of quantified formulas for which check was incomplete */
 std::unordered_set<Node> d_incompleteQuants;
};/* class ModelEngine */

}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5__THEORY__QUANTIFIERS__MODEL_ENGINE_H */
