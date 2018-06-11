/*********************                                                        */
/*! \file model_oracle.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2017 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief model_oracle
 **/

#include "cvc4_private.h"

#ifndef __CVC4__THEORY__QUANTIFIERS__MODEL_ORACLE_H
#define __CVC4__THEORY__QUANTIFIERS__MODEL_ORACLE_H

#include "theory/quantifiers_engine.h"
#include "theory/quantifiers/quant_util.h"

namespace CVC4 {
namespace theory {
namespace quantifiers {

/** ModelOracle
 * 
 */
class ModelOracle : public QuantifiersModule
{
public:
  ModelOracle( QuantifiersEngine * qe );
  ~ModelOracle(){}
  /** needs check */
  bool needsCheck(Theory::Effort e) override;
  /** needs model */
  QEffort needsModel(Theory::Effort e) override;
  /** check */
  void check(Theory::Effort e, QEffort quant_e) override;
  /** identify */
  std::string identify() const override { return "ModelOracle"; }
};


} /* CVC4::theory::quantifiers namespace */
} /* CVC4::theory namespace */
} /* CVC4 namespace */

#endif /* __CVC4__THEORY__QUANTIFIERS__MODEL_ORACLE_H */
