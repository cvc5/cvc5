/*********************                                                        */
/*! \file candidate_generator.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Morgan Deters, Andrew Reynolds, Clark Barrett
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2016 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Theory uf candidate generator
 **/

#include "cvc4_private.h"

#ifndef __CVC4__THEORY__QUANTIFIERS__CANDIDATE_GENERATOR_H
#define __CVC4__THEORY__QUANTIFIERS__CANDIDATE_GENERATOR_H

#include "theory/theory.h"
#include "theory/uf/equality_engine.h"

namespace CVC4 {
namespace theory {

namespace quantifiers {
  class TermArgTrie;
}

class QuantifiersEngine;

namespace inst {

/** base class for generating candidates for matching */
class CandidateGenerator {
protected:
  QuantifiersEngine* d_qe;
public:
  CandidateGenerator( QuantifiersEngine* qe ) : d_qe( qe ){}
  virtual ~CandidateGenerator(){}

  /** Get candidates functions.  These set up a context to get all match candidates.
      cg->reset( eqc );
      do{
        Node cand = cg->getNextCandidate();
        //.......
      }while( !cand.isNull() );

      eqc is the equivalence class you are searching in
  */
  virtual void reset( Node eqc ) = 0;
  virtual Node getNextCandidate() = 0;
  /** add candidate to list of nodes returned by this generator */
  virtual void addCandidate( Node n ) {}
  /** call this at the beginning of each instantiation round */
  virtual void resetInstantiationRound() = 0;
public:
  /** legal candidate */
  bool isLegalCandidate( Node n );
};/* class CandidateGenerator */

/** candidate generator queue (for manual candidate generation) */
class CandidateGeneratorQueue : public CandidateGenerator {
private:
  std::vector< Node > d_candidates;
  int d_candidate_index;
public:
  CandidateGeneratorQueue( QuantifiersEngine* qe ) : CandidateGenerator( qe ), d_candidate_index( 0 ){}
  ~CandidateGeneratorQueue() throw() {}

  void addCandidate( Node n );

  void resetInstantiationRound(){}
  void reset( Node eqc );
  Node getNextCandidate();
};/* class CandidateGeneratorQueue */

//the default generator
class CandidateGeneratorQE : public CandidateGenerator
{
  friend class CandidateGeneratorQEDisequal;
private:
  //operator you are looking for
  Node d_op;
  //the equality class iterator
  unsigned d_op_arity;
  std::vector< quantifiers::TermArgTrie* > d_tindex;
  std::vector< std::map< TNode, quantifiers::TermArgTrie >::iterator > d_tindex_iter;
  eq::EqClassIterator d_eqc_iter;
  //std::vector< Node > d_eqc;
  int d_term_iter;
  int d_term_iter_limit;
  bool d_using_term_db;
  enum {
    cand_term_db,
    cand_term_ident,
    cand_term_eqc,
    cand_term_tindex,
    cand_term_none,
  };
  short d_mode;
  bool isLegalOpCandidate( Node n );
  Node d_n;
  std::map< Node, bool > d_exclude_eqc;
public:
  CandidateGeneratorQE( QuantifiersEngine* qe, Node pat );
  ~CandidateGeneratorQE() throw() {}

  void resetInstantiationRound();
  void reset( Node eqc );
  Node getNextCandidate();
  void excludeEqc( Node r ) { d_exclude_eqc[r] = true; }
  bool isExcludedEqc( Node r ) { return d_exclude_eqc.find( r )!=d_exclude_eqc.end(); }
};

class CandidateGeneratorQELitEq : public CandidateGenerator
{
private:
  //the equality classes iterator
  eq::EqClassesIterator d_eq;
  //equality you are trying to match equalities for
  Node d_match_pattern;
  Node d_match_gterm;
  bool d_do_mgt;
public:
  CandidateGeneratorQELitEq( QuantifiersEngine* qe, Node mpat );
  ~CandidateGeneratorQELitEq() throw() {}

  void resetInstantiationRound();
  void reset( Node eqc );
  Node getNextCandidate();
};

class CandidateGeneratorQELitDeq : public CandidateGenerator
{
private:
  //the equality class iterator for false
  eq::EqClassIterator d_eqc_false;
  //equality you are trying to match disequalities for
  Node d_match_pattern;
  //type of disequality
  TypeNode d_match_pattern_type;
public:
  CandidateGeneratorQELitDeq( QuantifiersEngine* qe, Node mpat );
  ~CandidateGeneratorQELitDeq() throw() {}

  void resetInstantiationRound();
  void reset( Node eqc );
  Node getNextCandidate();
};

class CandidateGeneratorQEAll : public CandidateGenerator
{
private:
  //the equality classes iterator
  eq::EqClassesIterator d_eq;
  //equality you are trying to match equalities for
  Node d_match_pattern;
  TypeNode d_match_pattern_type;
  // quantifier/index for the variable we are matching
  Node d_f;
  unsigned d_index;
  //first time
  bool d_firstTime;
public:
  CandidateGeneratorQEAll( QuantifiersEngine* qe, Node mpat );
  ~CandidateGeneratorQEAll() throw() {}

  void resetInstantiationRound();
  void reset( Node eqc );
  Node getNextCandidate();
};

}/* CVC4::theory::inst namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */

#endif /* __CVC4__THEORY__QUANTIFIERS__CANDIDATE_GENERATOR_H */
