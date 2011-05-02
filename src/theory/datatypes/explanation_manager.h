/*********************                                                        */
/*! \file explanation_manager.h
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
 ** \brief Theory of datatypes.
 **
 ** Theory of datatypes.
 **/

#include "cvc4_private.h"

#ifndef __CVC4__THEORY__DATATYPES__EXPLANATION_MANAGER_H
#define __CVC4__THEORY__DATATYPES__EXPLANATION_MANAGER_H

#include "theory/theory.h"
#include "util/congruence_closure.h"
#include "util/datatype.h"
#include "util/hash.h"
#include "util/trans_closure.h"

#include <ext/hash_set>
#include <iostream>
#include <map>

namespace CVC4 {
namespace theory {
namespace datatypes {


class Explainer;

/** reason class */
class Reason { 
public:
  enum Rule {
    unspecified = 0,
    contradiction = 1,

    cc_coarse,

    //unification rules
    idt_unify,
    idt_cycle,
    idt_clash,
    //tester rules
    idt_taxiom,
    idt_tcong,
    idt_tclash,
    idt_texhaust,
    //other rules
    idt_inst,
    idt_collapse,
    idt_collapse2,

    input,
  };
public:
  Reason() : d_e( NULL ), d_isInput( true ){}
  Reason( Node n, unsigned r ) : d_node( n ), d_reason( r ), d_e( NULL ), d_isInput( false ) {}
  Reason( Explainer* e ) : d_reason( 0 ), d_e( e ), d_isInput( false ){}
  virtual ~Reason(){}
  Node d_node;
  unsigned d_reason;
  Explainer* d_e;
  bool d_isInput;
};

/** proof manager for theory lemmas */
class ProofManager {
protected:
  enum Effort {
    MIN_EFFORT = 0,
    STANDARD = 50,
    FULL_EFFORT = 100
  };/* enum Effort */
  /** map from nodes to a description of how they are explained */
  std::map< Node, std::pair< Node, unsigned > > d_exp;
  /** whether to produce proofs */
  Effort d_effort;
public:
  ProofManager( Effort effort = STANDARD ) : d_effort( effort ){}
  ~ProofManager(){}
  void setExplanation( Node n, Node jn, unsigned r = 0 );
  bool hasExplained( Node n ) { return d_exp.find( n )!=d_exp.end(); }
  Effort getEffort() { return d_effort; }
  void clear() { d_exp.clear(); }
  /** for debugging */
  Node getJustification( Node n ) { return d_exp[n].first; }
  unsigned getReason( Node n ) { return d_exp[n].second; }
};

class Explainer 
{
public:
  /** assert that n is true */
  virtual void assert( Node n ) = 0;
  /** get the explanation for n.  
      This should call pm->setExplanation( n1, jn1, r1 ) ... pm->setExplanation( nk, jnk, rk )
        for some set of Nodes n1...nk.
      Satisfies post conditions:
      - If pm->getEffort() = MAX_EFFORT, then each ( ni, jni, ri ) should be a precise
          application or rule ri, i.e. applying proof rule ri to jni derives ni.
      - If pm->getEffort() = STANDARD, then for each ( ni, jni, ri ), 
          jni is the (at least informal) justification for ni.
      - Return value should be a (possibly empty) conjunction of nodes n'1...n'k, where each n'i occurs 
          (as a conjunct) in jn1...jnk, but not in n1...nk.  
          For each of these literals n'i, assert( n'i ) was called.
      - either pm->setExplanation( n, ... ) is called, or n is the return value.
  */
  virtual Node explain( Node n, ProofManager* pm ) = 0;
};

template <class OutputChannel, class CongruenceOperatorList>
class CongruenceClosureExplainer : public Explainer
{
protected:
  //pointer to the congruence closure module
  CongruenceClosure<OutputChannel, CongruenceOperatorList>* d_cc;
public:
  CongruenceClosureExplainer(CongruenceClosure<OutputChannel, CongruenceOperatorList>* cc) :
    Explainer(),
    d_cc( cc ){
   }
  ~CongruenceClosureExplainer(){}
  /** assert that n is true */
  void assert( Node n ){
    Assert( n.getKind() == kind::EQUAL );
    d_cc->addEquality( n );
  }
  /** get the explanation for n */
  Node explain( Node n, ProofManager* pm ){
    Assert( n.getKind() == kind::EQUAL );
    if( pm->getEffort()==ProofManager::FULL_EFFORT ){
      //unsupported
      Assert( false );
      return Node::null();
    }else{
      Node exp = d_cc->explain( n[0], n[1] );
      if( exp!=n ){
        pm->setExplanation( n, exp, Reason::cc_coarse );
      }
      return exp;
    }
  }
};


class ExplanationManager : public Explainer
{
private:
  /** map from nodes and the reason for them */
  context::CDMap< Node, Reason, NodeHashFunction > d_drv_map;
  /** has conflict */
  context::CDO< bool > d_hasConflict;
  /** process the reason for node n */
  void process( Node n, NodeBuilder<>& nb, ProofManager* pm );
public:
  ExplanationManager(context::Context* c) : Explainer(), d_drv_map(c), d_hasConflict( c, false ){}
  ~ExplanationManager(){}

  /** assert that n is true (n is an input) */
  void assert( Node n ) { 
    //TODO: this can be optimized: 
    //  if the previous explanation for n was empty (n is a tautology), 
    //  then we should not claim it to be an input.
    Reason r = d_drv_map[n];
    r.d_isInput = true; 
  }
  /** n is explained */
  bool hasNode( Node n ) { return d_drv_map.find( n )!=d_drv_map.end(); }
  /** n is explained */
  bool hasConflict() { return d_hasConflict.get() || hasNode( NodeManager::currentNM()->mkConst(false) ); }
  /** jn is why n is true, by rule r */
  void addNode( Node n, Node jn, unsigned r = 0 ) { 
    if( !hasNode( n ) ){
      Assert( n!=jn );
      Debug("emanager") << "em::addNode: (" << jn << ", " << r << ") -> " << n << std::endl;
      d_drv_map[n] = Reason( jn, r ); 
    }
  }
  /** Explainer e can tell you why n is true in the current state.  */
  void addNode( Node n, Explainer* e ) {
    if( !hasNode( n ) ){
      Debug("emanager") << "em::addNodeEx: (" << e << ") -> " << n << std::endl;
      d_drv_map[n] = Reason( e ); 
    }
  }
  /** n is true by reason (axiom) r */
  void addNodeAxiom( Node n, unsigned r = 0 ) { addNode( n, Node::null(), r ); }
  /** conclude a contradiction by jn and reason r */
  void addNodeConflict( Node jn, unsigned r = 0 ){
    addNode( NodeManager::currentNM()->mkConst(false), jn, r );
    d_hasConflict.set( true );
  }
  /** get explanation for n 
      Requires pre conditions: TBD
      Satisfies post conditions:  TBD
  */
  Node explain( Node n, ProofManager* pm = NULL );
  /** get conflict */
  Node getConflict( ProofManager* pm = NULL ){
    return explain( NodeManager::currentNM()->mkConst(false), pm );
  }
};


}
}
}

#endif