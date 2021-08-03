/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Abstract management of models for TheoryEngine.
 */

#include "theory/model_manager.h"

#include "options/smt_options.h"
#include "options/theory_options.h"
#include "prop/prop_engine.h"
#include "smt/env.h"
#include "theory/quantifiers/first_order_model.h"
#include "theory/quantifiers/fmf/model_builder.h"
#include "theory/quantifiers_engine.h"
#include "theory/theory_engine.h"

namespace cvc5 {
namespace theory {

ModelManager::ModelManager(TheoryEngine& te, Env& env, EqEngineManager& eem)
    : d_te(te),
      d_env(env),
      d_eem(eem),
      d_modelEqualityEngine(nullptr),
      d_modelEqualityEngineAlloc(nullptr),
      d_model(new TheoryModel(
          env, "DefaultModel", options::assignFunctionValues())),
      d_modelBuilder(nullptr),
      d_modelBuilt(false),
      d_modelBuiltSuccess(false)
{
}

ModelManager::~ModelManager() {}

void ModelManager::finishInit(eq::EqualityEngineNotify* notify)
{
  // construct the model
  const LogicInfo& logicInfo = d_env.getLogicInfo();
  // Initialize the model and model builder.
  if (logicInfo.isQuantified())
  {
    QuantifiersEngine* qe = d_te.getQuantifiersEngine();
    Assert(qe != nullptr);
    d_modelBuilder = qe->getModelBuilder();
  }

  // make the default builder, e.g. in the case that the quantifiers engine does
  // not have a model builder
  if (d_modelBuilder == nullptr)
  {
    d_alocModelBuilder.reset(new TheoryEngineModelBuilder);
    d_modelBuilder = d_alocModelBuilder.get();
  }
  // notice that the equality engine of the model has yet to be assigned.
  initializeModelEqEngine(notify);
}

void ModelManager::resetModel()
{
  d_modelBuilt = false;
  d_modelBuiltSuccess = false;
  // Reset basic information on the model object
  d_model->reset();
}

bool ModelManager::buildModel()
{
  if (d_modelBuilt)
  {
    // already computed
    return d_modelBuiltSuccess;
  }
  // reset the flags now
  d_modelBuilt = true;
  d_modelBuiltSuccess = false;

  // prepare the model, which is specific to the manager
  if (!prepareModel())
  {
    Trace("model-builder") << "ModelManager: fail prepare model" << std::endl;
    return false;
  }

  // now, finish building the model
  d_modelBuiltSuccess = finishBuildModel();

  if (Trace.isOn("model-final"))
  {
    Trace("model-final") << "Final model:" << std::endl;
    Trace("model-final") << d_model->debugPrintModelEqc() << std::endl;
  }

  Trace("model-builder") << "ModelManager: model built success is "
                         << d_modelBuiltSuccess << std::endl;

  return d_modelBuiltSuccess;
}

bool ModelManager::isModelBuilt() const { return d_modelBuilt; }

void ModelManager::postProcessModel(bool incomplete)
{
  if (!d_modelBuilt)
  {
    // model not built, nothing to do
    return;
  }
  Trace("model-builder") << "ModelManager: post-process model..." << std::endl;
  // model construction should always succeed unless lemmas were added
  AlwaysAssert(d_modelBuiltSuccess);
  if (!options::produceModels())
  {
    return;
  }
  // Do post-processing of model from the theories (used for THEORY_SEP
  // to construct heap model)
  for (TheoryId theoryId = theory::THEORY_FIRST; theoryId < theory::THEORY_LAST;
       ++theoryId)
  {
    Theory* t = d_te.theoryOf(theoryId);
    if (t == nullptr)
    {
      // theory not active, skip
      continue;
    }
    Trace("model-builder-debug")
        << "  PostProcessModel on theory: " << theoryId << std::endl;
    t->postProcessModel(d_model.get());
  }
  // also call the model builder's post-process model
  d_modelBuilder->postProcessModel(incomplete, d_model.get());
}

theory::TheoryModel* ModelManager::getModel() { return d_model.get(); }

bool ModelManager::collectModelBooleanVariables()
{
  Trace("model-builder") << "  CollectModelInfo boolean variables" << std::endl;
  // Get value of the Boolean variables
  prop::PropEngine* propEngine = d_te.getPropEngine();
  std::vector<TNode> boolVars;
  propEngine->getBooleanVariables(boolVars);
  std::vector<TNode>::iterator it, iend = boolVars.end();
  bool hasValue, value;
  for (it = boolVars.begin(); it != iend; ++it)
  {
    TNode var = *it;
    hasValue = propEngine->hasValue(var, value);
    // Should we assert that hasValue is true?
    if (!hasValue)
    {
      Trace("model-builder-assertions")
          << "    has no value : " << var << std::endl;
      value = false;
    }
    Trace("model-builder-assertions")
        << "(assert" << (value ? " " : " (not ") << var
        << (value ? ");" : "));") << std::endl;
    if (!d_model->assertPredicate(var, value))
    {
      return false;
    }
  }
  return true;
}

void ModelManager::collectAssertedTerms(TheoryId tid,
                                        std::set<Node>& termSet,
                                        bool includeShared) const
{
  Theory* t = d_te.theoryOf(tid);
  // Collect all terms appearing in assertions
  context::CDList<Assertion>::const_iterator assert_it = t->facts_begin(),
                                             assert_it_end = t->facts_end();
  for (; assert_it != assert_it_end; ++assert_it)
  {
    collectTerms(tid, *assert_it, termSet);
  }

  if (includeShared)
  {
    // Add terms that are shared terms
    context::CDList<TNode>::const_iterator shared_it = t->shared_terms_begin(),
                                           shared_it_end =
                                               t->shared_terms_end();
    for (; shared_it != shared_it_end; ++shared_it)
    {
      collectTerms(tid, *shared_it, termSet);
    }
  }
}

void ModelManager::collectTerms(TheoryId tid,
                                TNode n,
                                std::set<Node>& termSet) const
{
  const std::set<Kind>& irrKinds = d_model->getIrrelevantKinds();
  std::vector<TNode> visit;
  TNode cur;
  visit.push_back(n);
  do
  {
    cur = visit.back();
    visit.pop_back();
    if (termSet.find(cur) != termSet.end())
    {
      // already visited
      continue;
    }
    Kind k = cur.getKind();
    // only add to term set if a relevant kind
    if (irrKinds.find(k) == irrKinds.end())
    {
      termSet.insert(cur);
    }
    // traverse owned terms, don't go under quantifiers
    if ((k == kind::NOT || k == kind::EQUAL || Theory::theoryOf(cur) == tid)
        && !cur.isClosure())
    {
      visit.insert(visit.end(), cur.begin(), cur.end());
    }
  } while (!visit.empty());
}

}  // namespace theory
}  // namespace cvc5
