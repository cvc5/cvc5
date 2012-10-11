/*********************                                                        */
/*! \file model_builder.h
 ** \verbatim
 ** Original author: ajreynol
 ** Major contributors: mdeters
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009-2012  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief Model Builder class
 **/

#include "cvc4_private.h"

#ifndef __CVC4__THEORY__QUANTIFIERS__MODEL_BUILDER_H
#define __CVC4__THEORY__QUANTIFIERS__MODEL_BUILDER_H

#include "theory/quantifiers_engine.h"
#include "theory/model.h"
#include "theory/uf/theory_uf_model.h"

namespace CVC4 {
namespace theory {
namespace quantifiers {

/** model builder class
  *  This class is capable of building candidate models based on the current quantified formulas
  *  that are asserted.  Use:
  *  (1) call ModelEngineBuilder::buildModel( m, false );, where m is a FirstOrderModel
  *  (2) if candidate model is determined to be a real model,
           then call ModelEngineBuilder::buildModel( m, true );
  */
class ModelEngineBuilder : public TheoryEngineModelBuilder
{
protected:
  //quantifiers engine
  QuantifiersEngine* d_qe;
  //the model we are working with
  context::CDO< FirstOrderModel* > d_curr_model;
  //map from operators to model preference data
  std::map< Node, uf::UfModelPreferenceData > d_uf_prefs;
  //built model uf
  std::map< Node, bool > d_uf_model_constructed;
  /** process build model */
  void processBuildModel( TheoryModel* m, bool fullModel );
protected:
  //analyze model
  void analyzeModel( FirstOrderModel* fm );
  //analyze quantifiers
  void analyzeQuantifiers( FirstOrderModel* fm );
  //build model
  void constructModel( FirstOrderModel* fm );
  //theory-specific build models
  void constructModelUf( FirstOrderModel* fm, Node op );
  //do InstGen techniques for quantifier, return number of lemmas produced
  int doInstGen( FirstOrderModel* fm, Node f );
public:
  ModelEngineBuilder( context::Context* c, QuantifiersEngine* qe );
  virtual ~ModelEngineBuilder(){}
  /** number of lemmas generated while building model */
  int d_addedLemmas;
  //consider axioms
  bool d_considerAxioms;
private:    ///information for InstGen
  //map from quantifiers to if are constant SAT
  std::map< Node, bool > d_quant_sat;
  //map from quantifiers to their selection literals
  std::map< Node, Node > d_quant_selection_lit;
  std::map< Node, std::vector< Node > > d_quant_selection_lit_candidates;
  //map from quantifiers to their selection literal terms
  std::map< Node, std::vector< Node > > d_quant_selection_lit_terms;
  //map from terms to the selection literals they exist in
  std::map< Node, Node > d_term_selection_lit;
  //map from operators to terms that appear in selection literals
  std::map< Node, std::vector< Node > > d_op_selection_terms;
public:
  //map from quantifiers to model basis match
  std::map< Node, InstMatch > d_quant_basis_match;
  //options
  bool optUseModel();
  bool optInstGen();
  bool optOneQuantPerRoundInstGen();
  // set effort
  void setEffort( int effort );
  /** statistics class */
  class Statistics {
  public:
    IntStat d_pre_sat_quant;
    IntStat d_pre_nsat_quant;
    Statistics();
    ~Statistics();
  };
  Statistics d_statistics;
  // is quantifier active?
  bool isQuantifierActive( Node f );
};/* class ModelEngineBuilder */

}/* CVC4::theory::quantifiers namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */

#endif /* __CVC4__THEORY__QUANTIFIERS__MODEL_BUILDER_H */
