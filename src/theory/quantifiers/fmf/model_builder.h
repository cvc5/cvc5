/*********************                                                        */
/*! \file model_builder.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Mathias Preiner
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Model Builder class
 **/

#include "cvc4_private.h"

#ifndef CVC4__THEORY__QUANTIFIERS__MODEL_BUILDER_H
#define CVC4__THEORY__QUANTIFIERS__MODEL_BUILDER_H

#include "expr/node.h"
#include "theory/quantifiers/first_order_model.h"
#include "theory/quantifiers/inst_match.h"
#include "theory/theory_model_builder.h"

namespace CVC4 {
namespace theory {
namespace quantifiers {


class QModelBuilder : public TheoryEngineModelBuilder
{
protected:
  //quantifiers engine
  QuantifiersEngine* d_qe;
  // must call preProcessBuildModelStd
  bool preProcessBuildModel(TheoryModel* m) override;
  bool preProcessBuildModelStd(TheoryModel* m);
  /** number of lemmas generated while building model */
  unsigned d_addedLemmas;
  unsigned d_triedLemmas;
public:
  QModelBuilder( context::Context* c, QuantifiersEngine* qe );

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
};

}/* CVC4::theory::quantifiers namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */

#endif /* CVC4__THEORY__QUANTIFIERS__MODEL_BUILDER_H */
