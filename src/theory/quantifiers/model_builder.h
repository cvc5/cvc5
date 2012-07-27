/*********************                                                        */
/*! \file model_builder.h
 ** \verbatim
 ** Original author: ajreynol
 ** Major contributors: mdeters
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009-2012  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief Model Builder class
 **/

#include "cvc4_private.h"

#ifndef __CVC4__QUANTIFIERS_MODEL_BUILDER_H
#define __CVC4__QUANTIFIERS_MODEL_BUILDER_H

#include "theory/quantifiers_engine.h"
#include "theory/model.h"
#include "theory/uf/theory_uf_model.h"

namespace CVC4 {
namespace theory {
namespace quantifiers {

//the model builder
class ModelEngineBuilder : public TheoryEngineModelBuilder
{
protected:
  //quantifiers engine
  QuantifiersEngine* d_qe;
  //map from operators to model preference data
  std::map< Node, uf::UfModelPreferenceData > d_uf_prefs;
  //built model uf
  std::map< Node, bool > d_uf_model_constructed;
  /** process build model */
  void processBuildModel( TheoryModel* m );
  /** choose representative for unconstrained equivalence class */
  Node chooseRepresentative( TheoryModel* m, Node eqc );
  /** bad representative */
  bool isBadRepresentative( Node n );
protected:
  //analyze model
  void analyzeModel( FirstOrderModel* fm );
  //analyze quantifiers
  void analyzeQuantifiers( FirstOrderModel* fm );
  //build model
  void finishBuildModel( FirstOrderModel* fm );
  //theory-specific build models
  void finishBuildModelUf( FirstOrderModel* fm, Node op );
  //do InstGen techniques for quantifier, return number of lemmas produced
  int doInstGen( FirstOrderModel* fm, Node f );
public:
  ModelEngineBuilder( QuantifiersEngine* qe );
  virtual ~ModelEngineBuilder(){}
  /** finish model */
  void finishProcessBuildModel( TheoryModel* m );
public:
  /** number of lemmas generated while building model */
  int d_addedLemmas;
  //map from quantifiers to if are constant SAT
  std::map< Node, bool > d_quant_sat;
  //map from quantifiers to the instantiation literals that their model is dependent upon
  std::map< Node, std::vector< Node > > d_quant_selection_lits;
public:
  //map from quantifiers to model basis match
  std::map< Node, InstMatch > d_quant_basis_match;
  //options
  bool optUseModel();
  bool optInstGen();
  bool optOneQuantPerRoundInstGen();
  /** statistics class */
  class Statistics {
  public:
    IntStat d_pre_sat_quant;
    IntStat d_pre_nsat_quant;
    Statistics();
    ~Statistics();
  };
  Statistics d_statistics;
};

}
}
}

#endif
