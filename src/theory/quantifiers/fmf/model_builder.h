/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Mathias Preiner, Aina Niemetz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Model Builder class.
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__QUANTIFIERS__MODEL_BUILDER_H
#define CVC5__THEORY__QUANTIFIERS__MODEL_BUILDER_H

#include "expr/node.h"
#include "theory/quantifiers/inst_match.h"
#include "theory/theory_model_builder.h"

namespace cvc5::internal {
namespace theory {
namespace quantifiers {

class FirstOrderModel;
class QuantifiersState;
class QuantifiersRegistry;
class QuantifiersInferenceManager;
class TermRegistry;

class QModelBuilder : public TheoryEngineModelBuilder
{
 protected:
  // must call preProcessBuildModelStd
  bool preProcessBuildModel(TheoryModel* m) override;
  bool preProcessBuildModelStd(TheoryModel* m);
  /** number of lemmas generated while building model */
  unsigned d_addedLemmas;
  unsigned d_triedLemmas;

 public:
  QModelBuilder(Env& env,
                QuantifiersState& qs,
                QuantifiersInferenceManager& qim,
                QuantifiersRegistry& qr,
                TermRegistry& tr);
  /** finish init, which sets the model object */
  virtual void finishInit();
  //do exhaustive instantiation  
  // 0 :  failed, but resorting to true exhaustive instantiation may work
  // >0 : success
  // <0 : failed
  virtual int doExhaustiveInstantiation( FirstOrderModel * fm, Node f, int effort ) { return false; }
  //whether to construct model
  virtual bool optUseModel();
  //debug model
  void debugModel(TheoryModel* m) override;
  //statistics 
  unsigned getNumAddedLemmas() { return d_addedLemmas; }
  unsigned getNumTriedLemmas() { return d_triedLemmas; }
  /** get the model we are using */
  FirstOrderModel* getModel();

 protected:
  /** The quantifiers state object */
  QuantifiersState& d_qstate;
  /** The quantifiers inference manager */
  QuantifiersInferenceManager& d_qim;
  /** Reference to the quantifiers registry */
  QuantifiersRegistry& d_qreg;
  /** Term registry */
  TermRegistry& d_treg;
  /** Pointer to the model object we are using */
  FirstOrderModel* d_model;
  /** The model object we have allocated */
  std::unique_ptr<FirstOrderModel> d_modelAloc;
};

}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5__THEORY__QUANTIFIERS__MODEL_BUILDER_H */
