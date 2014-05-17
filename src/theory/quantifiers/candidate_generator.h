/*********************                                                        */
/*! \file candidate_generator.h
 ** \verbatim
 ** Original author: Morgan Deters
 ** Major contributors: Andrew Reynolds
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2013  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
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

class QuantifiersEngine;

namespace inst {

/** base class for generating candidates for matching */
class CandidateGenerator {
public:
  CandidateGenerator(){}
  ~CandidateGenerator(){}

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
  static bool isLegalCandidate( Node n );
};/* class CandidateGenerator */

/** candidate generator queue (for manual candidate generation) */
class CandidateGeneratorQueue : public CandidateGenerator {
private:
  std::vector< Node > d_candidates;
  int d_candidate_index;
public:
  CandidateGeneratorQueue() : d_candidate_index( 0 ){}
  ~CandidateGeneratorQueue(){}

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
  //instantiator pointer
  QuantifiersEngine* d_qe;
  //the equality class iterator
  eq::EqClassIterator d_eqc_iter;
  //std::vector< Node > d_eqc;
  int d_term_iter;
  int d_term_iter_limit;
  bool d_using_term_db;
  enum {
    cand_term_db,
    cand_term_ident,
    cand_term_eqc,
  };
  short d_mode;
  bool isLegalOpCandidate( Node n );
  Node d_n;
public:
  CandidateGeneratorQE( QuantifiersEngine* qe, Node op );
  ~CandidateGeneratorQE(){}

  void resetInstantiationRound();
  void reset( Node eqc );
  Node getNextCandidate();
};

class CandidateGeneratorQELitEq : public CandidateGenerator
{
private:
  //the equality classes iterator
  eq::EqClassesIterator d_eq;
  //equality you are trying to match equalities for
  Node d_match_pattern;
  //einstantiator pointer
  QuantifiersEngine* d_qe;
public:
  CandidateGeneratorQELitEq( QuantifiersEngine* qe, Node mpat );
  ~CandidateGeneratorQELitEq(){}

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
  //einstantiator pointer
  QuantifiersEngine* d_qe;
public:
  CandidateGeneratorQELitDeq( QuantifiersEngine* qe, Node mpat );
  ~CandidateGeneratorQELitDeq(){}

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
  //einstantiator pointer
  QuantifiersEngine* d_qe;
public:
  CandidateGeneratorQEAll( QuantifiersEngine* qe, Node mpat );
  ~CandidateGeneratorQEAll(){}

  void resetInstantiationRound();
  void reset( Node eqc );
  Node getNextCandidate();
};

}/* CVC4::theory::inst namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */

#endif /* __CVC4__THEORY__QUANTIFIERS__CANDIDATE_GENERATOR_H */
