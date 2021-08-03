/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Aina Niemetz, Mathias Preiner
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Implementation of model builder class.
 */

#include "theory/quantifiers/fmf/model_builder.h"

#include "options/quantifiers_options.h"
#include "options/strings_options.h"
#include "theory/quantifiers/first_order_model.h"
#include "theory/quantifiers/fmf/model_engine.h"
#include "theory/quantifiers/instantiate.h"
#include "theory/quantifiers/quant_rep_bound_ext.h"
#include "theory/quantifiers/quantifiers_state.h"

using namespace std;
using namespace cvc5;
using namespace cvc5::kind;
using namespace cvc5::context;
using namespace cvc5::theory;
using namespace cvc5::theory::quantifiers;

QModelBuilder::QModelBuilder(QuantifiersState& qs,
                             QuantifiersInferenceManager& qim,
                             QuantifiersRegistry& qr,
                             TermRegistry& tr)
    : TheoryEngineModelBuilder(),
      d_addedLemmas(0),
      d_triedLemmas(0),
      d_qstate(qs),
      d_qim(qim),
      d_qreg(qr),
      d_treg(tr),
      d_model(nullptr)
{
}

void QModelBuilder::finishInit()
{
  // allocate the default model
  d_modelAloc.reset(new FirstOrderModel(d_qstate, d_qreg, d_treg));
  d_model = d_modelAloc.get();
}

bool QModelBuilder::optUseModel() {
  return options::mbqiMode() != options::MbqiMode::NONE || options::fmfBound()
         || options::stringExp();
}

bool QModelBuilder::preProcessBuildModel(TheoryModel* m) {
  return preProcessBuildModelStd( m );
}

bool QModelBuilder::preProcessBuildModelStd(TheoryModel* m) {
  d_addedLemmas = 0;
  d_triedLemmas = 0;
  if (options::fmfFunWellDefinedRelevant())
  {
    //traverse equality engine
    std::map< TypeNode, bool > eqc_usort;
    eq::EqClassesIterator eqcs_i =
        eq::EqClassesIterator(m->getEqualityEngine());
    while( !eqcs_i.isFinished() ){
      TypeNode tr = (*eqcs_i).getType();
      eqc_usort[tr] = true;
      ++eqcs_i;
    }
    //look at quantified formulas
    for (size_t i = 0, nquant = d_model->getNumAssertedQuantifiers();
         i < nquant;
         i++)
    {
      Node q = d_model->getAssertedQuantifier(i, true);
      if (d_model->isQuantifierActive(q))
      {
        //check if any of these quantified formulas can be set inactive
        if (q[0].getNumChildren() == 1)
        {
          TypeNode tn = q[0][0].getType();
          if (tn.getAttribute(AbsTypeFunDefAttribute()))
          {
            // we are allowed to assume the introduced type is empty
            if (eqc_usort.find(tn) == eqc_usort.end())
            {
              Trace("model-engine-debug")
                  << "Irrelevant function definition : " << q << std::endl;
              d_model->setQuantifierActive(q, false);
            }
          }
        }
      }
    }
  }
  return true;
}

void QModelBuilder::debugModel( TheoryModel* m ){
  //debug the model: cycle through all instantiations for all quantifiers, report ones that are not true
  if( Trace.isOn("quant-check-model") ){
    FirstOrderModel* fm = d_model;
    Trace("quant-check-model") << "Testing quantifier instantiations..." << std::endl;
    int tests = 0;
    int bad = 0;
    QuantifiersBoundInference& qbi = d_qreg.getQuantifiersBoundInference();
    Instantiate* inst = d_qim.getInstantiate();
    for( unsigned i=0; i<fm->getNumAssertedQuantifiers(); i++ ){
      Node f = fm->getAssertedQuantifier( i );
      std::vector< Node > vars;
      for( unsigned j=0; j<f[0].getNumChildren(); j++ ){
        vars.push_back( f[0][j] );
      }
      QRepBoundExt qrbe(qbi, fm);
      RepSetIterator riter(m->getRepSet(), &qrbe);
      if( riter.setQuantifier( f ) ){
        while( !riter.isFinished() ){
          tests++;
          std::vector< Node > terms;
          for (unsigned k = 0; k < riter.getNumTerms(); k++)
          {
            terms.push_back( riter.getCurrentTerm( k ) );
          }
          Node n = inst->getInstantiation(f, vars, terms);
          Node val = m->getValue(n);
          if (!val.isConst() || !val.getConst<bool>())
          {
            Trace("quant-check-model") << "*******  Instantiation " << n << " for " << std::endl;
            Trace("quant-check-model") << "         " << f << std::endl;
            Trace("quant-check-model") << "         Evaluates to " << val << std::endl;
            bad++;
          }
          riter.increment();
        }
        Trace("quant-check-model") << "Tested " << tests << " instantiations";
        if( bad>0 ){
          Trace("quant-check-model") << ", " << bad << " failed" << std::endl;
        }
        Trace("quant-check-model") << "." << std::endl;
      }else{
        if( riter.isIncomplete() ){
          Trace("quant-check-model") << "Warning: Could not test quantifier " << f << std::endl;
        }
      }
    }
  }
}
FirstOrderModel* QModelBuilder::getModel() { return d_model; }
