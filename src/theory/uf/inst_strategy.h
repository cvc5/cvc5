/*********************                                                        */
/*! \file inst_strategy.h
 ** \verbatim
 ** Original author: ajreynol
 ** Major contributors: none
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010, 2011  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief Theory uf instantiation strategies
 **/

#include "cvc4_private.h"

#ifndef __CVC4__INST_STRATEGY_H
#define __CVC4__INST_STRATEGY_H

#include "theory/quantifiers_engine.h"
#include "theory/quantifiers/trigger.h"

#include "context/context.h"
#include "context/context_mm.h"

#include "util/statistics_registry.h"
#include "theory/uf/theory_uf.h"

namespace CVC4 {
namespace theory {
namespace uf {

class InstantiatorTheoryUf;

//instantiation strategies

class InstStrategyCheckCESolved : public InstStrategy{
private:
  /** InstantiatorTheoryUf class */
  InstantiatorTheoryUf* d_th;
  /** is solved? */
  std::map< Node, bool > d_solved;
  /** calc if f is solved */
  void calcSolved( Node f );
  /** process functions */
  void processResetInstantiationRound( Theory::Effort effort );
  int process( Node f, Theory::Effort effort, int e );
public:
  InstStrategyCheckCESolved( InstantiatorTheoryUf* th, QuantifiersEngine* ie ) :
      InstStrategy( ie ), d_th( th ){}
  ~InstStrategyCheckCESolved(){}
  /** identify */
  std::string identify() const { return std::string("CheckCESolved"); }
};/* class InstStrategyCheckCESolved */

class InstStrategyUserPatterns : public InstStrategy{
private:
  /** InstantiatorTheoryUf class */
  InstantiatorTheoryUf* d_th;
  /** explicitly provided patterns */
  std::map< Node, std::vector< inst::Trigger* > > d_user_gen;
  /** counter for quantifiers */
  std::map< Node, int > d_counter;
  /** process functions */
  void processResetInstantiationRound( Theory::Effort effort );
  int process( Node f, Theory::Effort effort, int e );
public:
  InstStrategyUserPatterns( InstantiatorTheoryUf* th, QuantifiersEngine* ie ) :
      InstStrategy( ie ), d_th( th ){}
  ~InstStrategyUserPatterns(){}
public:
  /** add pattern */
  void addUserPattern( Node f, Node pat );
  /** get num patterns */
  int getNumUserGenerators( Node f ) { return (int)d_user_gen[f].size(); }
  /** get user pattern */
  inst::Trigger* getUserGenerator( Node f, int i ) { return d_user_gen[f][ i ]; }
  /** identify */
  std::string identify() const { return std::string("UserPatterns"); }
};/* class InstStrategyUserPatterns */

class InstStrategyAutoGenTriggers : public InstStrategy{
public:
  enum {
    RELEVANCE_NONE,
    RELEVANCE_DEFAULT,
  };
private:
  /** InstantiatorTheoryUf class */
  InstantiatorTheoryUf* d_th;
  /** trigger generation strategy */
  int d_tr_strategy;
  /** relevance strategy */
  int d_rlv_strategy;
  /** regeneration */
  bool d_regenerate;
  int d_regenerate_frequency;
  /** generate additional triggers */
  bool d_generate_additional;
  /** triggers for each quantifier */
  std::map< Node, std::map< inst::Trigger*, bool > > d_auto_gen_trigger;
  std::map< Node, int > d_counter;
  /** single, multi triggers for each quantifier */
  std::map< Node, std::vector< Node > > d_patTerms[2];
  std::map< Node, bool > d_is_single_trigger;
  std::map< Node, bool > d_single_trigger_gen;
  std::map< Node, bool > d_made_multi_trigger;
private:
  /** process functions */
  void processResetInstantiationRound( Theory::Effort effort );
  int process( Node f, Theory::Effort effort, int e );
  /** generate triggers */
  void generateTriggers( Node f );
public:
  InstStrategyAutoGenTriggers( InstantiatorTheoryUf* th, QuantifiersEngine* ie, int tstrt, int rstrt, int rgfr = -1 ) :
      InstStrategy( ie ), d_th( th ), d_tr_strategy( tstrt ), d_rlv_strategy( rstrt ), d_generate_additional( false ){
    setRegenerateFrequency( rgfr );
  }
  ~InstStrategyAutoGenTriggers(){}
public:
  /** get auto-generated trigger */
  inst::Trigger* getAutoGenTrigger( Node f );
  /** identify */
  std::string identify() const { return std::string("AutoGenTriggers"); }
  /** set regenerate frequency, if fr<0, turn off regenerate */
  void setRegenerateFrequency( int fr ){
    if( fr<0 ){
      d_regenerate = false;
    }else{
      d_regenerate_frequency = fr;
      d_regenerate = true;
    }
  }
  /** set generate additional */
  void setGenerateAdditional( bool val ) { d_generate_additional = val; }
};/* class InstStrategyAutoGenTriggers */

#if 0

class InstStrategyAddFailSplits : public InstStrategy{
private:
  /** InstantiatorTheoryUf class */
  InstantiatorTheoryUf* d_th;
  /** process functions */
  void processResetInstantiationRound( Theory::Effort effort );
  int process( Node f, Theory::Effort effort, int e );
public:
  InstStrategyAddFailSplits( InstantiatorTheoryUf* th, QuantifiersEngine* ie ) :
      InstStrategy( ie ), d_th( th ){}
  ~InstStrategyAddFailSplits(){}
  /** identify */
  std::string identify() const { return std::string("AddFailSplits"); }
};/* class InstStrategyAddFailSplits */

#endif /* 0 */

class InstStrategyFreeVariable : public InstStrategy{
private:
  /** InstantiatorTheoryUf class */
  InstantiatorTheoryUf* d_th;
  /** guessed instantiations */
  std::map< Node, bool > d_guessed;
  /** process functions */
  void processResetInstantiationRound( Theory::Effort effort );
  int process( Node f, Theory::Effort effort, int e );
public:
  InstStrategyFreeVariable( InstantiatorTheoryUf* th, QuantifiersEngine* ie ) :
      InstStrategy( ie ), d_th( th ){}
  ~InstStrategyFreeVariable(){}
  /** identify */
  std::string identify() const { return std::string("FreeVariable"); }
};/* class InstStrategyFreeVariable */

}/* CVC4::theory::uf namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */

#endif
