/*********************                                                        */
/*! \file model_builder.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Morgan Deters, Tim King
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2017 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Model Builder class
 **/

#include "cvc4_private.h"

#ifndef __CVC4__THEORY__QUANTIFIERS__MODEL_BUILDER_H
#define __CVC4__THEORY__QUANTIFIERS__MODEL_BUILDER_H

#include "theory/quantifiers_engine.h"
#include "theory/theory_model_builder.h"
#include "theory/uf/theory_uf_model.h"

namespace CVC4 {
namespace theory {
namespace quantifiers {


class QModelBuilder : public TheoryEngineModelBuilder
{
protected:
  //quantifiers engine
  QuantifiersEngine* d_qe;
  bool preProcessBuildModel(TheoryModel* m); //must call preProcessBuildModelStd
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
  virtual void debugModel( TheoryModel* m );
  //statistics 
  unsigned getNumAddedLemmas() { return d_addedLemmas; }
  unsigned getNumTriedLemmas() { return d_triedLemmas; }
};





class TermArgBasisTrie {
public:
  /** the data */
  std::map< Node, TermArgBasisTrie > d_data;
  /** add term to the trie */
  bool addTerm(FirstOrderModel* fm, Node n, unsigned argIndex = 0);
};/* class TermArgBasisTrie */

/** model builder class
  *  This class is capable of building candidate models based on the current quantified formulas
  *  that are asserted.  Use:
  *  (1) call QModelBuilder::buildModel( m, false );, where m is a FirstOrderModel
  *  (2) if candidate model is determined to be a real model,
           then call QModelBuilder::buildModel( m, true );
  */
class QModelBuilderIG : public QModelBuilder
{
  typedef context::CDHashMap<Node, bool, NodeHashFunction> BoolMap;

 protected:
  BoolMap d_basisNoMatch;
  //map from operators to model preference data
  std::map< Node, uf::UfModelPreferenceData > d_uf_prefs;
  //built model uf
  std::map< Node, bool > d_uf_model_constructed;
  //whether inst gen was done
  bool d_didInstGen;
  /** process build model */
  virtual bool processBuildModel( TheoryModel* m );

 protected:
  //reset
  virtual void reset( FirstOrderModel* fm ) = 0;
  //initialize quantifiers, return number of lemmas produced
  virtual int initializeQuantifier(Node f, Node fp, FirstOrderModel* fm);
  //analyze model
  virtual void analyzeModel( FirstOrderModel* fm );
  //analyze quantifiers
  virtual void analyzeQuantifier( FirstOrderModel* fm, Node f ) = 0;
  //do InstGen techniques for quantifier, return number of lemmas produced
  virtual int doInstGen( FirstOrderModel* fm, Node f ) = 0;
  //theory-specific build models
  virtual void constructModelUf( FirstOrderModel* fm, Node op ) = 0;

 protected:
  //map from quantifiers to if are SAT
  //std::map< Node, bool > d_quant_sat;
  //which quantifiers have been initialized
  std::map< Node, bool > d_quant_basis_match_added;
  //map from quantifiers to model basis match
  std::map< Node, InstMatch > d_quant_basis_match;

 protected:  // helper functions
  /** term has constant definition */
  bool hasConstantDefinition( Node n );

 public:
  QModelBuilderIG( context::Context* c, QuantifiersEngine* qe );

 public:
  /** statistics class */
  class Statistics {
  public:
    IntStat d_num_quants_init;
    IntStat d_num_partial_quants_init;
    IntStat d_init_inst_gen_lemmas;
    IntStat d_inst_gen_lemmas;
    IntStat d_eval_formulas;
    IntStat d_eval_uf_terms;
    IntStat d_eval_lits;
    IntStat d_eval_lits_unknown;
    Statistics();
    ~Statistics();
  };
  Statistics d_statistics;
  // is term selected
  virtual bool isTermSelected( Node n ) { return false; }
  /** quantifier has inst-gen definition */
  virtual bool hasInstGen( Node f ) = 0;
  /** did inst gen this round? */
  bool didInstGen() { return d_didInstGen; }
  // is quantifier active?
  bool isQuantifierActive( Node f );
  //do exhaustive instantiation
  int doExhaustiveInstantiation( FirstOrderModel * fm, Node f, int effort );

  //temporary stats
  int d_numQuantSat;
  int d_numQuantInstGen;
  int d_numQuantNoInstGen;
  int d_numQuantNoSelForm;
  //temporary stat
  int d_instGenMatches;
};/* class QModelBuilder */


class QModelBuilderDefault : public QModelBuilderIG
{
 private:  /// information for (old) InstGen
  // map from quantifiers to their selection literals
  std::map< Node, Node > d_quant_selection_lit;
  std::map< Node, std::vector< Node > > d_quant_selection_lit_candidates;
  //map from quantifiers to their selection literal terms
  std::map< Node, std::vector< Node > > d_quant_selection_lit_terms;
  //map from terms to the selection literals they exist in
  std::map< Node, Node > d_term_selection_lit;
  //map from operators to terms that appear in selection literals
  std::map< Node, std::vector< Node > > d_op_selection_terms;
  //get selection score
  int getSelectionScore( std::vector< Node >& uf_terms );

 protected:
  //reset
  void reset(FirstOrderModel* fm) override;
  //analyze quantifier
  void analyzeQuantifier(FirstOrderModel* fm, Node f) override;
  //do InstGen techniques for quantifier, return number of lemmas produced
  int doInstGen(FirstOrderModel* fm, Node f) override;
  //theory-specific build models
  void constructModelUf(FirstOrderModel* fm, Node op) override;

 protected:
  std::map< Node, QuantPhaseReq > d_phase_reqs;

 public:
  QModelBuilderDefault( context::Context* c, QuantifiersEngine* qe ) : QModelBuilderIG( c, qe ){}

  //options
  bool optReconsiderFuncConstants() { return true; }
  //has inst gen
  bool hasInstGen(Node f) override
  {
    return !d_quant_selection_lit[f].isNull();
  }
};

}/* CVC4::theory::quantifiers namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */

#endif /* __CVC4__THEORY__QUANTIFIERS__MODEL_BUILDER_H */
