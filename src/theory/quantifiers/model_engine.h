/*********************                                                        */
/*! \file model_engine.h
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
 ** \brief Model Engine classes
 **/

#include "cvc4_private.h"

#ifndef __CVC4__MODEL_ENGINE_H
#define __CVC4__MODEL_ENGINE_H

#include "theory/quantifiers_engine.h"
#include "theory/quantifiers/theory_quantifiers.h"
#include "theory/model.h"
#include "theory/uf/theory_uf_model.h"
#include "theory/quantifiers/relevant_domain.h"

namespace CVC4 {
namespace theory {

namespace uf{
  class StrongSolverTheoryUf;
}

namespace quantifiers {


//the model builder
class ModelEngineBuilder : public TheoryEngineModelBuilder
{
protected:
  //quantifiers engine
  QuantifiersEngine* d_qe;
  //map from operators to model preference data
  std::map< Node, uf::UfModelPreferenceData > d_uf_prefs;
  /** choose representative */
  Node chooseRepresentative( TheoryModel* tm, Node eqc );
  /** use constants for representatives */
  void processBuildModel( TheoryModel* m );
  //analyze quantifiers
  void analyzeQuantifiers( FirstOrderModel* fm );
  //build model
  void finishBuildModel( FirstOrderModel* fm );
  //theory-specific build models
  void finishBuildModelUf( FirstOrderModel* fm, uf::UfModel& model );
  //do InstGen techniques for quantifier, return number of lemmas produced
  int doInstGen( FirstOrderModel* fm, Node f );
public:
  ModelEngineBuilder( QuantifiersEngine* qe );
  virtual ~ModelEngineBuilder(){}
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

class ModelEngine : public QuantifiersModule
{
  friend class uf::UfModel;
  friend class RepSetIterator;
private:
  /** builder class */
  ModelEngineBuilder d_builder;
private:    //data maintained globally:
  //which quantifiers have been initialized
  std::map< Node, bool > d_quant_init;
private:    //analysis of current model:
  //relevant domain
  RelevantDomain d_rel_domain;
private:
  //options
  bool optOneInstPerQuantRound();
  bool optUseRelevantDomain();
  bool optOneQuantPerRound();
private:
  //initialize quantifiers, return number of lemmas produced
  int initializeQuantifier( Node f );
  //exhaustively instantiate quantifier (possibly using mbqi), return number of lemmas produced
  int exhaustiveInstantiate( Node f, bool useRelInstDomain = false );
private:
  //temporary statistics
  int d_triedLemmas;
  int d_testLemmas;
  int d_totalLemmas;
  int d_relevantLemmas;
public:
  ModelEngine( QuantifiersEngine* qe );
  ~ModelEngine(){}
public:
  void check( Theory::Effort e );
  void registerQuantifier( Node f );
  void assertNode( Node f );
  Node explain(TNode n){ return Node::null(); }
  void propagate( Theory::Effort level ){}
  void debugPrint( const char* c );
public:
  /** statistics class */
  class Statistics {
  public:
    IntStat d_inst_rounds;
    IntStat d_eval_formulas;
    IntStat d_eval_eqs;
    IntStat d_eval_uf_terms;
    IntStat d_num_quants_init;
    IntStat d_num_quants_init_fail;
    Statistics();
    ~Statistics();
  };
  Statistics d_statistics;
};

}
}
}

#endif
