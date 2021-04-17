/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Mathias Preiner, Gereon Kremer
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
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

namespace cvc5 {
namespace theory {
namespace quantifiers {

class FirstOrderModel;
class QuantifiersState;
class QuantifiersRegistry;
class QuantifiersInferenceManager;

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
  QModelBuilder(QuantifiersState& qs,
                QuantifiersRegistry& qr,
                QuantifiersInferenceManager& qim);

  //do exhaustive instantiation  
  // 0 :  failed, but resorting to true exhaustive instantiation may work
  // >0 : success
  // <0 : failed
  virtual int doExhaustiveInstantiation( FirstOrderModel * fm, Node f, int effort ) { return false; }
  //whether to construct model
  virtual bool optUseModel();
  /** exist instantiation ? */
  virtual bool existsInstantiation( Node f, InstMatch& m, bool modEq = true, bool modInst = false ) { return false; }
  //debug model
  void debugModel(TheoryModel* m) override;
  //statistics 
  unsigned getNumAddedLemmas() { return d_addedLemmas; }
  unsigned getNumTriedLemmas() { return d_triedLemmas; }

 protected:
  /** Pointer to quantifiers engine */
  QuantifiersEngine* d_qe;
  /** The quantifiers state object */
  QuantifiersState& d_qstate;
  /** Reference to the quantifiers registry */
  QuantifiersRegistry& d_qreg;
  /** The quantifiers inference manager */
  quantifiers::QuantifiersInferenceManager& d_qim;
};

}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5

#endif /* CVC5__THEORY__QUANTIFIERS__MODEL_BUILDER_H */
