/*********************                                                        */
/*! \file theory_uf_instantiator.h
 ** \verbatim
 ** Original author: ajreynol
 ** Major contributors: bobot
 ** Minor contributors (to current version): mdeters
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009-2012  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief Theory uf instantiator
 **/

#include "cvc4_private.h"

#ifndef __CVC4__THEORY_UF_INSTANTIATOR_H
#define __CVC4__THEORY_UF_INSTANTIATOR_H

#include "theory/uf/inst_strategy.h"

#include "context/context.h"
#include "context/context_mm.h"
#include "context/cdchunk_list.h"

#include "util/statistics_registry.h"
#include "theory/uf/theory_uf.h"
#include "theory/quantifiers/trigger.h"
#include "theory/quantifiers/inst_match_generator.h"
#include "util/ntuple.h"
#include "context/cdqueue.h"

namespace CVC4 {
namespace theory {

namespace quantifiers{
  class TermDb;
}

namespace uf {

class InstantiatorTheoryUf : public Instantiator{
  friend class ::CVC4::theory::inst::InstMatchGenerator;
  friend class ::CVC4::theory::quantifiers::TermDb;
protected:
  typedef context::CDHashMap<Node, bool, NodeHashFunction> BoolMap;
  typedef context::CDHashMap<Node, int, NodeHashFunction> IntMap;
  typedef context::CDChunkList<Node> NodeList;
  typedef context::CDHashMap<Node, NodeList*, NodeHashFunction> NodeLists;
  /** map to representatives used */
  //std::map< Node, Node > d_ground_reps;
protected:
  /** instantiation strategies */
  InstStrategyUserPatterns* d_isup;
public:
  InstantiatorTheoryUf(context::Context* c, CVC4::theory::QuantifiersEngine* qe, Theory* th);
  ~InstantiatorTheoryUf() {}
  /** assertNode method */
  void assertNode( Node assertion );
  /** Pre-register a term.  Done one time for a Node, ever. */
  void preRegisterTerm( Node t );
  /** identify */
  std::string identify() const { return std::string("InstantiatorTheoryUf"); }
  /** debug print */
  void debugPrint( const char* c );
  /** add user pattern */
  void addUserPattern( Node f, Node pat );
private:
  /** reset instantiation */
  void processResetInstantiationRound( Theory::Effort effort );
  /** calculate matches for quantifier f at effort */
  int process( Node f, Theory::Effort effort, int e );
public:
  /** statistics class */
  class Statistics {
  public:
    //IntStat d_instantiations;
    IntStat d_instantiations_ce_solved;
    IntStat d_instantiations_e_induced;
    IntStat d_instantiations_user_pattern;
    IntStat d_instantiations_guess;
    IntStat d_instantiations_auto_gen;
    IntStat d_instantiations_auto_gen_min;
    IntStat d_splits;
    Statistics();
    ~Statistics();
  };
  Statistics d_statistics;
public:
  /** the base match */
  std::map< Node, InstMatch > d_baseMatch;
public:
  /** general queries about equality */
  bool hasTerm( Node a );
  bool areEqual( Node a, Node b );
  bool areDisequal( Node a, Node b );
  Node getRepresentative( Node a );
  Node getInternalRepresentative( Node a );
  eq::EqualityEngine* getEqualityEngine();
  void getEquivalenceClass( Node a, std::vector< Node >& eqc );
  /** general creators of candidate generators */
  rrinst::CandidateGenerator* getRRCanGenClasses();
  rrinst::CandidateGenerator* getRRCanGenClass();
  /** new node */
  void newEqClass( TNode n );
  /** merge */
  void merge( TNode a, TNode b );
  /** assert terms are disequal */
  void assertDisequal( TNode a, TNode b, TNode reason );
private:
  /** triggers */
  std::map< Node, std::vector< inst::Trigger* > > d_op_triggers;
public:
  /** register trigger (for eager quantifier instantiation) */
  void registerTrigger( inst::Trigger* tr, Node op );
public:
  /** output eq class */
  void outputEqClass( const char* c, Node n );
};/* class InstantiatorTheoryUf */

/** equality query object using instantiator theory uf */
class EqualityQueryInstantiatorTheoryUf : public EqualityQuery
{
private:
  /** pointer to instantiator uf class */
  InstantiatorTheoryUf* d_ith;
public:
  EqualityQueryInstantiatorTheoryUf( InstantiatorTheoryUf* ith ) : d_ith( ith ){}
  ~EqualityQueryInstantiatorTheoryUf(){}
  /** general queries about equality */
  bool hasTerm( Node a ) { return d_ith->hasTerm( a ); }
  Node getRepresentative( Node a ) { return d_ith->getRepresentative( a ); }
  bool areEqual( Node a, Node b ) { return d_ith->areEqual( a, b ); }
  bool areDisequal( Node a, Node b ) { return d_ith->areDisequal( a, b ); }
  eq::EqualityEngine* getEngine() { return d_ith->getEqualityEngine(); }
  void getEquivalenceClass( Node a, std::vector< Node >& eqc ) { d_ith->getEquivalenceClass( a, eqc ); }
}; /* EqualityQueryInstantiatorTheoryUf */

}
}/* CVC4::theory namespace */
}/* CVC4 namespace */

#endif /* __CVC4__THEORY_UF_INSTANTIATOR_H */
