/*********************                                                        */
/*! \file model_engine.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Mathias Preiner, Morgan Deters
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Model Engine class
 **/

#include "cvc4_private.h"

#ifndef CVC4__THEORY__QUANTIFIERS__MODEL_ENGINE_H
#define CVC4__THEORY__QUANTIFIERS__MODEL_ENGINE_H

#include "theory/quantifiers/fmf/model_builder.h"
#include "theory/quantifiers/quant_util.h"
#include "theory/theory_model.h"

namespace CVC4 {
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
  // set of quantified formulas for which check was incomplete
  std::vector< Node > d_incomplete_quants;
  int d_addedLemmas;
  int d_triedLemmas;
  int d_totalLemmas;
public:
  ModelEngine( context::Context* c, QuantifiersEngine* qe );
  virtual ~ModelEngine();
public:
 bool needsCheck(Theory::Effort e) override;
 QEffort needsModel(Theory::Effort e) override;
 void reset_round(Theory::Effort e) override;
 void check(Theory::Effort e, QEffort quant_e) override;
 bool checkComplete() override;
 bool checkCompleteFor(Node q) override;
 void registerQuantifier(Node f) override;
 void assertNode(Node f) override;
 Node explain(TNode n) { return Node::null(); }
 void debugPrint(const char* c);
 /** Identify this module */
 std::string identify() const override { return "ModelEngine"; }
};/* class ModelEngine */

}/* CVC4::theory::quantifiers namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */

#endif /* CVC4__THEORY__QUANTIFIERS__MODEL_ENGINE_H */
