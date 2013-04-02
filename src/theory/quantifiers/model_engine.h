/*********************                                                        */
/*! \file model_engine.h
 ** \verbatim
 ** Original author: Morgan Deters
 ** Major contributors: Andrew Reynolds
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2013  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief Model Engine class
 **/

#include "cvc4_private.h"

#ifndef __CVC4__THEORY__QUANTIFIERS__MODEL_ENGINE_H
#define __CVC4__THEORY__QUANTIFIERS__MODEL_ENGINE_H

#include "theory/quantifiers_engine.h"
#include "theory/quantifiers/model_builder.h"
#include "theory/model.h"
#include "theory/quantifiers/relevant_domain.h"

namespace CVC4 {
namespace theory {
namespace quantifiers {

class ModelEngine : public QuantifiersModule
{
  friend class RepSetIterator;
private:
  /** builder class */
  ModelEngineBuilder* d_builder;
private:    //analysis of current model:
  //relevant domain
  RelevantDomain d_rel_domain;
  //is the exhaustive instantiation incomplete?
  bool d_incomplete_check;
private:
  //options
  bool optOneInstPerQuantRound();
  bool optUseRelevantDomain();
  bool optOneQuantPerRound();
  bool optExhInstEvalSkipMultiple();
private:
  enum{
    check_model_full,
    check_model_no_inst_gen,
  };
  //check model
  int checkModel( int checkOption );
  //exhaustively instantiate quantifier (possibly using mbqi), return number of lemmas produced
  int exhaustiveInstantiate( Node f, bool useRelInstDomain = false );
private:
  //temporary statistics
  int d_triedLemmas;
  int d_testLemmas;
  int d_totalLemmas;
  int d_relevantLemmas;
public:
  ModelEngine( context::Context* c, QuantifiersEngine* qe );
  ~ModelEngine(){}
  //get the builder
  ModelEngineBuilder* getModelBuilder() { return d_builder; }
public:
  void check( Theory::Effort e );
  void registerQuantifier( Node f );
  void assertNode( Node f );
  Node explain(TNode n){ return Node::null(); }
  void debugPrint( const char* c );
public:
  /** statistics class */
  class Statistics {
  public:
    IntStat d_inst_rounds;
    IntStat d_eval_formulas;
    IntStat d_eval_uf_terms;
    IntStat d_eval_lits;
    IntStat d_eval_lits_unknown;
    IntStat d_exh_inst_lemmas;
    Statistics();
    ~Statistics();
  };
  Statistics d_statistics;
};/* class ModelEngine */

}/* CVC4::theory::quantifiers namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */

#endif /* __CVC4__THEORY__QUANTIFIERS__MODEL_ENGINE_H */
