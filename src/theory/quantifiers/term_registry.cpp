/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Andres Noetzli, Gereon Kremer
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2025 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Term registry class.
 */

#include "theory/quantifiers/term_registry.h"

#include "options/base_options.h"
#include "options/quantifiers_options.h"
#include "options/smt_options.h"
#include "theory/quantifiers/entailment_check.h"
#include "theory/quantifiers/first_order_model.h"
#include "theory/quantifiers/fmf/first_order_model_fmc.h"
#include "theory/quantifiers/ho_term_database.h"
#include "theory/quantifiers/oracle_checker.h"
#include "theory/quantifiers/quantifiers_attributes.h"
#include "theory/quantifiers/quantifiers_state.h"
#include "theory/quantifiers/term_util.h"

namespace cvc5::internal {
namespace theory {
namespace quantifiers {

TermRegistry::TermRegistry(Env& env,
                           QuantifiersState& qs,
                           QuantifiersRegistry& qr)
    : EnvObj(env),
      d_termEnum(new TermEnumeration),
      d_termPools(new TermPools(env, qs)),
      d_termDb(logicInfo().isHigherOrder() ? new HoTermDb(env, qs, qr)
                                           : new TermDb(env, qs, qr)),
      d_echeck(new EntailmentCheck(env, qs, *d_termDb.get())),
      d_sygusTdb(nullptr),
      d_vtsCache(new VtsTermCache(env)),
      d_ievalMan(new ieval::InstEvaluatorManager(env, qs, *d_termDb.get())),
      d_qmodel(nullptr)
{
  if (options().quantifiers.oracles)
  {
    d_ochecker.reset(new OracleChecker(env));
  }
  if (options().quantifiers.cegqiBv)
  {
    // if doing instantiation for BV, need the inverter class
    d_bvInvert.reset(new BvInverter(env.getRewriter()));
  }
  if (options().quantifiers.sygus || options().quantifiers.sygusInst)
  {
    // must be constructed here since it is required for datatypes finistInit
    d_sygusTdb.reset(new TermDbSygus(env, qs));
  }
  Trace("quant-engine-debug") << "Initialize quantifiers engine." << std::endl;
}

void TermRegistry::finishInit(FirstOrderModel* fm,
                              QuantifiersInferenceManager* qim)
{
  d_qmodel = fm;
  d_termDb->finishInit(qim);
  if (d_sygusTdb.get())
  {
    d_sygusTdb->finishInit(qim);
  }
}

void TermRegistry::addQuantifierBody(TNode n) { addTermInternal(n, true); }

void TermRegistry::eqNotifyNewClass(TNode t) { addTermInternal(t, false); }

void TermRegistry::eqNotifyMerge(TNode t1, TNode t2)
{
  // notify the term database
  d_termDb->eqNotifyMerge(t1, t2);
}

void TermRegistry::addTermInternal(TNode n, bool withinQuant)
{
  // don't add terms in quantifier bodies
  if (withinQuant && !options().quantifiers.registerQuantBodyTerms)
  {
    return;
  }
  d_termDb->addTerm(n);
  if (d_sygusTdb.get()
      && options().quantifiers.sygusEvalUnfoldMode
             != options::SygusEvalUnfoldMode::NONE)
  {
    d_sygusTdb->getEvalUnfold()->registerEvalTerm(n);
  }
}

Node TermRegistry::getTermForType(TypeNode tn)
{
  if (tn.isClosedEnumerable())
  {
    return d_termEnum->getEnumerateTerm(tn, 0);
  }
  return d_termDb->getOrMakeTypeGroundTerm(tn);
}

void TermRegistry::getTermsForPool(Node p, std::vector<Node>& terms)
{
  if (p.getKind() == Kind::SET_UNIVERSE)
  {
    // get all ground terms of the given type
    TypeNode ptn = p.getType().getSetElementType();
    size_t nterms = d_termDb->getNumTypeGroundTerms(ptn);
    for (size_t i = 0; i < nterms; i++)
    {
      terms.push_back(d_termDb->getTypeGroundTerm(ptn, i));
    }
  }
  else
  {
    d_termPools->getTermsForPool(p, terms);
  }
}

void TermRegistry::declarePool(Node p, const std::vector<Node>& initValue)
{
  d_termPools->registerPool(p, initValue);
}

void TermRegistry::processInstantiation(Node q,
                                        const std::vector<Node>& terms,
                                        bool success)
{
  d_termPools->processInstantiation(q, terms, success);
}
void TermRegistry::processSkolemization(Node q,
                                        const std::vector<Node>& skolems)
{
  d_termPools->processSkolemization(q, skolems);
}

TermDb* TermRegistry::getTermDatabase() const { return d_termDb.get(); }

TermDbSygus* TermRegistry::getTermDatabaseSygus() const
{
  return d_sygusTdb.get();
}

OracleChecker* TermRegistry::getOracleChecker() const
{
  return d_ochecker.get();
}

EntailmentCheck* TermRegistry::getEntailmentCheck() const
{
  return d_echeck.get();
}

TermEnumeration* TermRegistry::getTermEnumeration() const
{
  return d_termEnum.get();
}

TermPools* TermRegistry::getTermPools() const { return d_termPools.get(); }

VtsTermCache* TermRegistry::getVtsTermCache() const { return d_vtsCache.get(); }

BvInverter* TermRegistry::getBvInverter() const { return d_bvInvert.get(); }

ieval::InstEvaluatorManager* TermRegistry::getInstEvaluatorManager() const
{
  return d_ievalMan.get();
}

ieval::InstEvaluator* TermRegistry::getEvaluator(Node q,
                                                 ieval::TermEvaluatorMode tev)
{
  return d_ievalMan->getEvaluator(q, tev);
}

FirstOrderModel* TermRegistry::getModel() const { return d_qmodel; }

}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal
