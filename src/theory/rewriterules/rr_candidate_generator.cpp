/*********************                                                        */
/*! \file rr_candidate_generator.cpp
 ** \verbatim
 ** Original author: ajreynol
 ** Major contributors: none
 ** Minor contributors (to current version): mdeters
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009-2012  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief Implementation of rr candidate generator class
 **/

#include "theory/rewriterules/rr_candidate_generator.h"
#include "theory/theory_engine.h"
#include "theory/uf/theory_uf.h"
#include "theory/quantifiers/term_database.h"

using namespace std;
using namespace CVC4;
using namespace CVC4::kind;
using namespace CVC4::context;
using namespace CVC4::theory;
using namespace CVC4::theory::rrinst;

GenericCandidateGeneratorClasses::GenericCandidateGeneratorClasses(QuantifiersEngine * qe){
  for(TheoryId i = THEORY_FIRST; i < theory::THEORY_LAST; ++i){
    if(qe->getInstantiator(i) != NULL)
      d_can_gen[i] = qe->getInstantiator(i)->getRRCanGenClasses();
    else d_can_gen[i] = NULL;
  }
}

GenericCandidateGeneratorClasses::~GenericCandidateGeneratorClasses(){
  for(TheoryId i = THEORY_FIRST; i < theory::THEORY_LAST; ++i){
    delete(d_can_gen[i]);
  }
}

void GenericCandidateGeneratorClasses::resetInstantiationRound(){
  for(TheoryId i = THEORY_FIRST; i < theory::THEORY_LAST; ++i){
    if(d_can_gen[i] != NULL) d_can_gen[i]->resetInstantiationRound();
  }
  d_can_gen_id=THEORY_FIRST;
}

void GenericCandidateGeneratorClasses::reset(TNode eqc){
  Assert(eqc.isNull());
  for(TheoryId i = THEORY_FIRST; i < theory::THEORY_LAST; ++i){
    if(d_can_gen[i] != NULL) d_can_gen[i]->reset(eqc);
  }
  d_can_gen_id=THEORY_FIRST;
  lookForNextTheory();
}

TNode GenericCandidateGeneratorClasses::getNextCandidate(){
  Assert(THEORY_FIRST <= d_can_gen_id && d_can_gen_id <= THEORY_LAST);
  /** No more */
  if(d_can_gen_id == THEORY_LAST) return TNode::null();
  /** Try with this theory */
  TNode cand = d_can_gen[d_can_gen_id]->getNextCandidate();
  if( !cand.isNull() ) return cand;
  lookForNextTheory();
  return getNextCandidate();
}

void GenericCandidateGeneratorClasses::lookForNextTheory(){
  do{ /* look for the next available generator */
    ++d_can_gen_id;
  } while( d_can_gen_id < THEORY_LAST && d_can_gen[d_can_gen_id] == NULL);
}

GenericCandidateGeneratorClass::GenericCandidateGeneratorClass(QuantifiersEngine * qe): d_qe(qe) {
  for(TheoryId i = THEORY_FIRST; i < theory::THEORY_LAST; ++i){
    if(d_qe->getInstantiator(i) != NULL)
      d_can_gen[i] = d_qe->getInstantiator(i)->getRRCanGenClass();
    else d_can_gen[i] = NULL;
  }
}

GenericCandidateGeneratorClass::~GenericCandidateGeneratorClass(){
  for(TheoryId i = THEORY_FIRST; i < theory::THEORY_LAST; ++i){
    delete(d_can_gen[i]);
  }
}

void GenericCandidateGeneratorClass::resetInstantiationRound(){
  for(TheoryId i = THEORY_FIRST; i < theory::THEORY_LAST; ++i){
    if(d_can_gen[i] != NULL) d_can_gen[i]->resetInstantiationRound();
  }
  d_can_gen_id=THEORY_FIRST;
}

void GenericCandidateGeneratorClass::reset(TNode eqc){
  for(TheoryId i = THEORY_FIRST; i < theory::THEORY_LAST; ++i){
    if(d_can_gen[i] != NULL) d_can_gen[i]->reset(eqc);
  }
  d_can_gen_id=THEORY_FIRST;
  d_node = eqc;
  lookForNextTheory();
}

TNode GenericCandidateGeneratorClass::getNextCandidate(){
  Assert(THEORY_FIRST <= d_can_gen_id && d_can_gen_id <= THEORY_LAST);
  /** No more */
  if(d_can_gen_id == THEORY_LAST) return TNode::null();
  /** Try with this theory */
  TNode cand = d_can_gen[d_can_gen_id]->getNextCandidate();
  if( !cand.isNull() ) return cand;
  lookForNextTheory();
  return getNextCandidate();
}

void GenericCandidateGeneratorClass::lookForNextTheory(){
  do{ /* look for the next available generator, where the element is */
    ++d_can_gen_id;
  } while(
          d_can_gen_id < THEORY_LAST &&
          (d_can_gen[d_can_gen_id] == NULL ||
           !d_qe->getInstantiator( d_can_gen_id )->hasTerm( d_node ))
          );
}
