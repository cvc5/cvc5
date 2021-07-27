/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Morgan Deters, Kshitij Bansal
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Implementation of model engine class.
 */

#include "theory/quantifiers/fmf/model_engine.h"

#include "options/quantifiers_options.h"
#include "theory/quantifiers/first_order_model.h"
#include "theory/quantifiers/fmf/full_model_check.h"
#include "theory/quantifiers/instantiate.h"
#include "theory/quantifiers/quant_rep_bound_ext.h"
#include "theory/quantifiers/quantifiers_attributes.h"
#include "theory/quantifiers/term_database.h"

using namespace cvc5::kind;
using namespace cvc5::context;

namespace cvc5 {
namespace theory {
namespace quantifiers {

//Model Engine constructor
ModelEngine::ModelEngine(QuantifiersState& qs,
                         QuantifiersInferenceManager& qim,
                         QuantifiersRegistry& qr,
                         TermRegistry& tr,
                         QModelBuilder* builder)
    : QuantifiersModule(qs, qim, qr, tr),
      d_incomplete_check(true),
      d_addedLemmas(0),
      d_triedLemmas(0),
      d_totalLemmas(0),
      d_builder(builder)
{

}

ModelEngine::~ModelEngine() {

}

bool ModelEngine::needsCheck( Theory::Effort e ) {
  return e==Theory::EFFORT_LAST_CALL;
}

QuantifiersModule::QEffort ModelEngine::needsModel(Theory::Effort e)
{
  if( options::mbqiInterleave() ){
    return QEFFORT_STANDARD;
  }else{
    return QEFFORT_MODEL;
  }
}

void ModelEngine::reset_round( Theory::Effort e ) {
  d_incomplete_check = true;
}
void ModelEngine::check(Theory::Effort e, QEffort quant_e)
{
  bool doCheck = false;
  if( options::mbqiInterleave() ){
    doCheck = quant_e == QEFFORT_STANDARD && d_qim.hasPendingLemma();
  }
  if( !doCheck ){
    doCheck = quant_e == QEFFORT_MODEL;
  }
  if( doCheck ){
    Assert(!d_qstate.isInConflict());
    int addedLemmas = 0;

    //the following will test that the model satisfies all asserted universal quantifiers by
    // (model-based) exhaustive instantiation.
    double clSet = 0;
    if( Trace.isOn("model-engine") ){
      Trace("model-engine") << "---Model Engine Round---" << std::endl;
      clSet = double(clock())/double(CLOCKS_PER_SEC);
    }
    Trace("model-engine-debug") << "Check model..." << std::endl;
    d_incomplete_check = false;
    // print debug
    if (Trace.isOn("fmf-model-complete"))
    {
      Trace("fmf-model-complete") << std::endl;
      debugPrint("fmf-model-complete");
    }
    // successfully built an acceptable model, now check it
    addedLemmas += checkModel();

    if( Trace.isOn("model-engine") ){
      double clSet2 = double(clock())/double(CLOCKS_PER_SEC);
      Trace("model-engine") << "Finished model engine, time = " << (clSet2-clSet) << std::endl;
    }

    if( addedLemmas==0 ){
      Trace("model-engine-debug")
          << "No lemmas added, incomplete = "
          << (d_incomplete_check || !d_incompleteQuants.empty()) << std::endl;
      // cvc5 will answer SAT or unknown
      if( Trace.isOn("fmf-consistent") ){
        Trace("fmf-consistent") << std::endl;
        debugPrint("fmf-consistent");
      }
    }
  }
}

bool ModelEngine::checkComplete(IncompleteId& incId)
{
  if (d_incomplete_check)
  {
    incId = IncompleteId::QUANTIFIERS_FMF;
    return false;
  }
  return true;
}

bool ModelEngine::checkCompleteFor( Node q ) {
  return d_incompleteQuants.find(q) == d_incompleteQuants.end();
}

void ModelEngine::registerQuantifier( Node f ){
  if( Trace.isOn("fmf-warn") ){
    bool canHandle = true;
    for( unsigned i=0; i<f[0].getNumChildren(); i++ ){
      TypeNode tn = f[0][i].getType();
      if( !tn.isSort() ){
        if (!d_qstate.isFiniteType(tn))
        {
          if( tn.isInteger() ){
            if( !options::fmfBound() ){
              canHandle = false;
            }
          }else{
            canHandle = false;
          }
        }
      }
    }
    if( !canHandle ){
      Trace("fmf-warn") << "Warning : Model Engine : may not be able to answer SAT because of formula : " << f << std::endl;
    }
  }
}

int ModelEngine::checkModel(){
  FirstOrderModel* fm = d_treg.getModel();

  //for debugging, setup
  for (std::map<TypeNode, std::vector<Node> >::iterator it =
           fm->getRepSetPtr()->d_type_reps.begin();
       it != fm->getRepSetPtr()->d_type_reps.end();
       ++it)
  {
    if( it->first.isSort() ){
      Trace("model-engine") << "Cardinality( " << it->first << " )" << " = " << it->second.size() << std::endl;
      Trace("model-engine-debug") << "        Reps : ";
      for( size_t i=0; i<it->second.size(); i++ ){
        Trace("model-engine-debug") << it->second[i] << "  ";
      }
      Trace("model-engine-debug") << std::endl;
      Trace("model-engine-debug") << "   Term reps : ";
      for( size_t i=0; i<it->second.size(); i++ ){
        Node r = fm->getInternalRepresentative(it->second[i], Node::null(), 0);
        if (r.isNull())
        {
          // there was an invalid equivalence class
          d_incomplete_check = true;
        }
        Trace("model-engine-debug") << r << " ";
      }
      Trace("model-engine-debug") << std::endl;
      Node mbt = fm->getModelBasisTerm(it->first);
      Trace("model-engine-debug") << "  Basis term : " << mbt << std::endl;
    }
  }

  d_triedLemmas = 0;
  d_addedLemmas = 0;
  d_totalLemmas = 0;
  //for statistics
  if( Trace.isOn("model-engine") ){
    for( unsigned i=0; i<fm->getNumAssertedQuantifiers(); i++ ){
      Node f = fm->getAssertedQuantifier( i );
      if (fm->isQuantifierActive(f) && shouldProcess(f))
      {
        int totalInst = 1;
        for( unsigned j=0; j<f[0].getNumChildren(); j++ ){
          TypeNode tn = f[0][j].getType();
          if (fm->getRepSet()->hasType(tn))
          {
            totalInst =
                totalInst * (int)fm->getRepSet()->getNumRepresentatives(tn);
          }
        }
        d_totalLemmas += totalInst;
      }
    }
  }

  Trace("model-engine-debug") << "Do exhaustive instantiation..." << std::endl;
  // FMC uses two sub-effort levels
  int e_max = options::mbqiMode() == options::MbqiMode::FMC
                  ? 2
                  : (options::mbqiMode() == options::MbqiMode::TRUST ? 0 : 1);
  for( int e=0; e<e_max; e++) {
    d_incompleteQuants.clear();
    for( unsigned i=0; i<fm->getNumAssertedQuantifiers(); i++ ){
      Node q = fm->getAssertedQuantifier( i, true );
      Trace("fmf-exh-inst") << "-> Exhaustive instantiate " << q << ", effort = " << e << "..." << std::endl;
      //determine if we should check this quantifier
      if (!fm->isQuantifierActive(q))
      {
        Trace("fmf-exh-inst") << "-> Inactive : " << q << std::endl;
        continue;
      }
      if (!shouldProcess(q))
      {
        Trace("fmf-exh-inst") << "-> Not processed : " << q << std::endl;
        d_incompleteQuants.insert(q);
        continue;
      }
      exhaustiveInstantiate(q, e);
      if (d_qstate.isInConflict())
      {
        break;
      }
    }
    if( d_addedLemmas>0 ){
      break;
    }else{
      Assert(!d_qstate.isInConflict());
    }
  }

  //print debug information
  if (d_qstate.isInConflict())
  {
    Trace("model-engine") << "Conflict, added lemmas = ";
  }else{
    Trace("model-engine") << "Added Lemmas = ";
  } 
  Trace("model-engine") << d_addedLemmas << " / " << d_triedLemmas << " / ";
  Trace("model-engine") << d_totalLemmas << std::endl;
  return d_addedLemmas;
}



void ModelEngine::exhaustiveInstantiate( Node f, int effort ){
  //first check if the builder can do the exhaustive instantiation
  unsigned prev_alem = d_builder->getNumAddedLemmas();
  unsigned prev_tlem = d_builder->getNumTriedLemmas();
  FirstOrderModel* fm = d_treg.getModel();
  int retEi = d_builder->doExhaustiveInstantiation(fm, f, effort);
  if( retEi!=0 ){
    if( retEi<0 ){
      Trace("fmf-exh-inst") << "-> Builder determined complete instantiation was impossible." << std::endl;
      d_incompleteQuants.insert(f);
    }else{
      Trace("fmf-exh-inst") << "-> Builder determined instantiation(s)." << std::endl;
    }
    d_triedLemmas += d_builder->getNumTriedLemmas() - prev_tlem;
    d_addedLemmas += d_builder->getNumAddedLemmas() - prev_alem;
  }else{
    if( Trace.isOn("fmf-exh-inst-debug") ){
      Trace("fmf-exh-inst-debug") << "   Instantiation Constants: ";
      for( size_t i=0; i<f[0].getNumChildren(); i++ ){
        Trace("fmf-exh-inst-debug")
            << d_qreg.getInstantiationConstant(f, i) << " ";
      }
      Trace("fmf-exh-inst-debug") << std::endl;
    }
    QuantifiersBoundInference& qbi = d_qreg.getQuantifiersBoundInference();
    //create a rep set iterator and iterate over the (relevant) domain of the quantifier
    QRepBoundExt qrbe(qbi, fm);
    RepSetIterator riter(fm->getRepSet(), &qrbe);
    if( riter.setQuantifier( f ) ){
      Trace("fmf-exh-inst") << "...exhaustive instantiation set, incomplete=" << riter.isIncomplete() << "..." << std::endl;
      if( !riter.isIncomplete() ){
        int triedLemmas = 0;
        int addedLemmas = 0;
        Instantiate* inst = d_qim.getInstantiate();
        while( !riter.isFinished() && ( addedLemmas==0 || !options::fmfOneInstPerRound() ) ){
          //instantiation was not shown to be true, construct the match
          InstMatch m( f );
          for (unsigned i = 0; i < riter.getNumTerms(); i++)
          {
            m.set(d_qstate, i, riter.getCurrentTerm(i));
          }
          Debug("fmf-model-eval") << "* Add instantiation " << m << std::endl;
          triedLemmas++;
          //add as instantiation
          if (inst->addInstantiation(f,
                                     m.d_vals,
                                     InferenceId::QUANTIFIERS_INST_FMF_EXH,
                                     Node::null(),
                                     true))
          {
            addedLemmas++;
            if (d_qstate.isInConflict())
            {
              break;
            }
          }else{
            Debug("fmf-model-eval") << "* Failed Add instantiation " << m << std::endl;
          }
          riter.increment();
        }
        d_addedLemmas += addedLemmas;
        d_triedLemmas += triedLemmas;
      }
    }else{
      Trace("fmf-exh-inst") << "...exhaustive instantiation did set, incomplete=" << riter.isIncomplete() << "..." << std::endl;
    }
    //if the iterator is incomplete, we will return unknown instead of sat if no instantiations are added this round
    if( riter.isIncomplete() ){
      d_incompleteQuants.insert(f);
    }
  }
}

void ModelEngine::debugPrint( const char* c ){
  if (Trace.isOn(c))
  {
    Trace(c) << "Quantifiers: " << std::endl;
    FirstOrderModel* m = d_treg.getModel();
    for (size_t i = 0, nquant = m->getNumAssertedQuantifiers(); i < nquant; i++)
    {
      Node q = m->getAssertedQuantifier(i);
      if (d_qreg.hasOwnership(q, this))
      {
        Trace(c) << "   ";
        if (!m->isQuantifierActive(q))
        {
          Trace(c) << "*Inactive* ";
        }
        else
        {
          Trace(c) << "           ";
        }
        Trace(c) << q << std::endl;
      }
    }
  }
}

bool ModelEngine::shouldProcess(Node q)
{
  if (!d_qreg.hasOwnership(q, this))
  {
    return false;
  }
  // if finite model finding or fmf bound is on, we process everything
  if (options::finiteModelFind() || options::fmfBound())
  {
    return true;
  }
  // otherwise, we are only using model-based instantiation for internal
  // quantified formulas
  QuantAttributes& qattr = d_qreg.getQuantAttributes();
  return qattr.isInternal(q);
}

}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5
