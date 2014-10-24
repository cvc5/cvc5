/*********************                                                        */
/*! \file inst_strategy_e_matching.h
 ** \verbatim
 ** Original author: Andrew Reynolds
 ** Major contributors: Morgan Deters
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2014  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief E matching instantiation strategies
 **/

#include "cvc4_private.h"

#ifndef __CVC4__INST_STRATEGY_E_MATCHING_H
#define __CVC4__INST_STRATEGY_E_MATCHING_H

#include "theory/quantifiers_engine.h"
#include "theory/quantifiers/trigger.h"

#include "context/context.h"
#include "context/context_mm.h"

#include "util/statistics_registry.h"
#include "theory/quantifiers/instantiation_engine.h"

namespace CVC4 {
namespace theory {
namespace quantifiers {

//instantiation strategies

class InstStrategyUserPatterns : public InstStrategy{
private:
  /** explicitly provided patterns */
  std::map< Node, std::vector< inst::Trigger* > > d_user_gen;
  /** waiting to be generated patterns */
  std::map< Node, std::vector< std::vector< Node > > > d_user_gen_wait;
  /** counter for quantifiers */
  std::map< Node, int > d_counter;
  /** process functions */
  void processResetInstantiationRound( Theory::Effort effort );
  int process( Node f, Theory::Effort effort, int e );
public:
  InstStrategyUserPatterns( QuantifiersEngine* ie ) :
      InstStrategy( ie ){}
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
  /** trigger generation strategy */
  int d_tr_strategy;
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
  //processed trigger this round
  std::map< Node, std::map< inst::Trigger*, bool > > d_processed_trigger;
  //instantiation no patterns
  std::map< Node, std::vector< Node > > d_user_no_gen;
private:
  /** process functions */
  void processResetInstantiationRound( Theory::Effort effort );
  int process( Node f, Theory::Effort effort, int e );
  /** generate triggers */
  void generateTriggers( Node f, Theory::Effort effort, int e, int & status );
  /** has user patterns */
  bool hasUserPatterns( Node f );
  /** has user patterns */
  std::map< Node, bool > d_hasUserPatterns;
public:
  /** tstrt is the type of triggers to use (maximum depth, minimum depth, or all)
      rstrt is the relevance setting for trigger (use only relevant triggers vs. use all)
      rgfr is the frequency at which triggers are generated */
  InstStrategyAutoGenTriggers( QuantifiersEngine* qe, int tstrt,  int rgfr = -1 );
  ~InstStrategyAutoGenTriggers(){}
public:
  /** get auto-generated trigger */
  inst::Trigger* getAutoGenTrigger( Node f );
  /** identify */
  std::string identify() const { return std::string("AutoGenTriggers"); }
  /** add pattern */
  void addUserNoPattern( Node f, Node pat );
};/* class InstStrategyAutoGenTriggers */

class InstStrategyFreeVariable : public InstStrategy{
private:
  /** guessed instantiations */
  std::map< Node, bool > d_guessed;
  /** process functions */
  void processResetInstantiationRound( Theory::Effort effort );
  int process( Node f, Theory::Effort effort, int e );
public:
  InstStrategyFreeVariable( QuantifiersEngine* qe ) :
      InstStrategy( qe ){}
  ~InstStrategyFreeVariable(){}
  /** identify */
  std::string identify() const { return std::string("FreeVariable"); }
};/* class InstStrategyFreeVariable */

}
}/* CVC4::theory namespace */
}/* CVC4 namespace */

#endif
