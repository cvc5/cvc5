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
  //initialize quantifiers, return number of lemmas produced
  int initializeQuantifier( Node f );
  //analyze model
  void analyzeModel( FirstOrderModel* fm );
  //analyze quantifiers
  virtual void analyzeQuantifiers( FirstOrderModel* fm ) = 0;
  //build model
  void constructModel( FirstOrderModel* fm );
  //theory-specific build models
  void constructModelUf( FirstOrderModel* fm, Node op );
  /** set default value */
  virtual bool shouldSetDefaultValue( Node n ) = 0;
  //do InstGen techniques for quantifier, return number of lemmas produced
  virtual int doInstGen( FirstOrderModel* fm, Node f ) = 0;
protected:
  //map from quantifiers to if are SAT
  std::map< Node, bool > d_quant_sat;
  //which quantifiers have been initialized
  std::map< Node, bool > d_quant_init;
  //map from quantifiers to model basis match
  std::map< Node, InstMatch > d_quant_basis_match;
public:
  ModelEngineBuilder( context::Context* c, QuantifiersEngine* qe );
  virtual ~ModelEngineBuilder(){}
  /** number of lemmas generated while building model */
  int d_addedLemmas;
  //consider axioms
  bool d_considerAxioms;
  // set effort
  void setEffort( int effort );
public:
  //options
  virtual bool optUseModel();
  virtual bool optInstGen();
  virtual bool optOneQuantPerRoundInstGen();
  virtual bool optReconsiderFuncConstants();
  /** statistics class */
  class Statistics {
  public:
    IntStat d_pre_sat_quant;
    IntStat d_pre_nsat_quant;
    IntStat d_num_quants_init;
    IntStat d_num_quants_init_fail;
    Statistics();
    ~Statistics();
  };
  Statistics d_statistics;
  // is quantifier active?
  bool isQuantifierActive( Node f );
  // is term selected
  virtual bool isTermSelected( Node n ) { return false; }
};/* class ModelEngineBuilder */


class ModelEngineBuilderDefault : public ModelEngineBuilder
{
private:    ///information for (old) InstGen
  //map from quantifiers to their selection literals
  std::map< Node, Node > d_quant_selection_lit;
  std::map< Node, std::vector< Node > > d_quant_selection_lit_candidates;
  //map from quantifiers to their selection literal terms
  std::map< Node, std::vector< Node > > d_quant_selection_lit_terms;
  //map from terms to the selection literals they exist in
  std::map< Node, Node > d_term_selection_lit;
  //map from operators to terms that appear in selection literals
  std::map< Node, std::vector< Node > > d_op_selection_terms;
protected:
  //analyze quantifiers
  void analyzeQuantifiers( FirstOrderModel* fm );
  //do InstGen techniques for quantifier, return number of lemmas produced
  int doInstGen( FirstOrderModel* fm, Node f );
  /** set default value */
  bool shouldSetDefaultValue( Node n );
private:
  //analyze quantifier
  void analyzeQuantifier( FirstOrderModel* fm, Node f );
public:
  ModelEngineBuilderDefault( context::Context* c, QuantifiersEngine* qe ) : ModelEngineBuilder( c, qe ){}
  ~ModelEngineBuilderDefault(){}
  //options
  bool optReconsiderFuncConstants() { return true; }
};

class ModelEngineBuilderInstGen : public ModelEngineBuilder
{
private:    ///information for (new) InstGen
  //map from quantifiers to their selection literals
  std::map< Node, Node > d_quant_selection_formula;
  //map of terms that are selected
  std::map< Node, bool > d_term_selected;
  //a collection of InstMatch structures produced for each quantifier
  std::map< Node, inst::InstMatchTrie > d_sub_quant_inst_trie;
  //children quantifiers for each quantifier, each is an instance
  std::map< Node, std::vector< Node > > d_sub_quants;
  //instances of each partial instantiation with respect to the root
  std::map< Node, InstMatch > d_sub_quant_inst;
  //*root* parent of each partial instantiation
  std::map< Node, Node > d_sub_quant_parent;
protected:
  //analyze quantifiers
  void analyzeQuantifiers( FirstOrderModel* fm );
  //do InstGen techniques for quantifier, return number of lemmas produced
  int doInstGen( FirstOrderModel* fm, Node f );
  /** set default value */
  bool shouldSetDefaultValue( Node n );
private:
  //analyze quantifier
  void analyzeQuantifier( FirstOrderModel* fm, Node f );
  //get selection formula for quantifier body
  Node getSelectionFormula( Node fn, Node n, bool polarity, int useOption );
  //set selected terms in term
  void setSelectedTerms( Node s );
  //is usable selection literal
  bool isUsableSelectionLiteral( Node n, int useOption );
  // get parent quantifier
  Node getParentQuantifier( Node f );
  //get parent quantifier match
  void getParentQuantifierMatch( InstMatch& mp, Node fp, InstMatch& m, Node f );
public:
  ModelEngineBuilderInstGen( context::Context* c, QuantifiersEngine* qe ) : ModelEngineBuilder( c, qe ){}
  ~ModelEngineBuilderInstGen(){}
  // is term selected
  bool isTermSelected( Node n ) { return d_term_selected.find( n )!=d_term_selected.end(); }
};

}/* CVC4::theory::quantifiers namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */

#endif /* __CVC4__THEORY__QUANTIFIERS__MODEL_BUILDER_H */
