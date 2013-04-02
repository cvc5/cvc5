/*********************                                                        */
/*! \file rr_candidate_generator.cpp
 ** \verbatim
 ** Original author: Morgan Deters
 ** Major contributors: Andrew Reynolds
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2013  New York University and The University of Iowa
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

GenericCandidateGeneratorClasses::GenericCandidateGeneratorClasses(QuantifiersEngine * qe) : d_qe(qe){
  d_master_can_gen = new eq::rrinst::CandidateGeneratorTheoryEeClasses(d_qe->getMasterEqualityEngine());
}

GenericCandidateGeneratorClasses::~GenericCandidateGeneratorClasses(){
  delete d_master_can_gen;
}

void GenericCandidateGeneratorClasses::resetInstantiationRound(){
  d_master_can_gen->resetInstantiationRound();
}

void GenericCandidateGeneratorClasses::reset(TNode eqc){
  d_master_can_gen->reset(eqc);
}

TNode GenericCandidateGeneratorClasses::getNextCandidate(){
  return d_master_can_gen->getNextCandidate();
}


GenericCandidateGeneratorClass::GenericCandidateGeneratorClass(QuantifiersEngine * qe): d_qe(qe) {
  d_master_can_gen = new eq::rrinst::CandidateGeneratorTheoryEeClass(d_qe->getMasterEqualityEngine());
}

GenericCandidateGeneratorClass::~GenericCandidateGeneratorClass(){
  delete d_master_can_gen;
}

void GenericCandidateGeneratorClass::resetInstantiationRound(){
  d_master_can_gen->resetInstantiationRound();
}

void GenericCandidateGeneratorClass::reset(TNode eqc){
  d_master_can_gen->reset(eqc);
}

TNode GenericCandidateGeneratorClass::getNextCandidate(){
  return d_master_can_gen->getNextCandidate();
}

