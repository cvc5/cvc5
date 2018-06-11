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

#include <unordered_map>

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
  /** reset round */
  void reset_round( Theory::Effort e ) override;
  /** needs check */
  bool needsCheck(Theory::Effort e) override;
  /** needs model */
  QEffort needsModel(Theory::Effort e) override;
  /** check */
  void check(Theory::Effort e, QEffort quant_e) override;
  /** Check was complete for quantified formula q */
  bool checkCompleteFor( Node q ) override;
  /** identify */
  std::string identify() const override { return "ModelOracle"; }
 private:
  /** check success */
  bool d_check_success;
  /** clean model value 
   * 
   * 
   */
  Node cleanModelValue( Node n, std::unordered_map<TNode, Node, TNodeHashFunction> visited);
  /** map from terms to fresh variables */
  std::unordered_map< Node, Node, NodeHashFunction > d_fresh_var;
  /** get or make fresh variable for */
  Node getOrMkFreshVariableFor(Node c);
  /** list of fresh variables per type */
  std::map< TypeNode, std::vector< Node > > d_fresh_var_type;
};


} /* CVC4::theory::quantifiers namespace */
} /* CVC4::theory namespace */
} /* CVC4 namespace */

#endif /* __CVC4__THEORY__QUANTIFIERS__MODEL_ORACLE_H */
