/*********************                                                        */
/*! \file model_engine.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Morgan Deters, Andrew Reynolds, Tim King
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2016 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Model Engine class
 **/

#include "cvc4_private.h"

#ifndef __CVC4__THEORY__QUANTIFIERS__MODEL_ENGINE_H
#define __CVC4__THEORY__QUANTIFIERS__MODEL_ENGINE_H

#include "theory/quantifiers_engine.h"
#include "theory/quantifiers/model_builder.h"
#include "theory/theory_model.h"

namespace CVC4 {
namespace theory {
namespace quantifiers {

class ModelEngine : public QuantifiersModule
{
  friend class RepSetIterator;
private:
  //options
  bool optOneQuantPerRound();
private:
  //check model
  int checkModel();
  //consider quantified formula
  bool considerQuantifiedFormula( Node q );
  //exhaustively instantiate quantifier (possibly using mbqi)
  void exhaustiveInstantiate( Node f, int effort = 0 );
private:
  //temporary statistics
  //is the exhaustive instantiation incomplete?
  bool d_incomplete_check;
  int d_addedLemmas;
  int d_triedLemmas;
  int d_totalLemmas;
public:
  ModelEngine( context::Context* c, QuantifiersEngine* qe );
  virtual ~ModelEngine();
public:
  bool needsCheck( Theory::Effort e );
  unsigned needsModel( Theory::Effort e );
  void reset_round( Theory::Effort e );
  void check( Theory::Effort e, unsigned quant_e );
  bool checkComplete();
  void registerQuantifier( Node f );
  void assertNode( Node f );
  Node explain(TNode n){ return Node::null(); }
  void debugPrint( const char* c );
public:
  /** statistics class */
  class Statistics {
  public:
    IntStat d_inst_rounds;
    IntStat d_exh_inst_lemmas;
    IntStat d_mbqi_inst_lemmas;
    Statistics();
    ~Statistics();
  };
  Statistics d_statistics;
  /** Identify this module */
  std::string identify() const { return "ModelEngine"; }
};/* class ModelEngine */

}/* CVC4::theory::quantifiers namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */

#endif /* __CVC4__THEORY__QUANTIFIERS__MODEL_ENGINE_H */
