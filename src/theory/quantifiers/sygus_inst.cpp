/*********************                                                        */
/*! \file sygus_inst.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Mathias Preiner, Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief SyGuS instantiator class.
 **/

#include "theory/quantifiers/sygus_inst.h"

#include <sstream>
#include <unordered_set>

#include "expr/node_algorithm.h"
#include "theory/datatypes/sygus_datatype_utils.h"
#include "theory/quantifiers/sygus/sygus_enumerator.h"
#include "theory/quantifiers/sygus/sygus_grammar_cons.h"
#include "theory/quantifiers/sygus/synth_engine.h"
#include "theory/quantifiers_engine.h"
#include "theory/theory_engine.h"

namespace CVC4 {
namespace theory {
namespace quantifiers {

SygusInst::SygusInst(QuantifiersEngine* qe)
    : QuantifiersModule(qe),
      d_lemma_cache(qe->getUserContext()),
      d_ce_lemma_added(qe->getUserContext())
{
}

bool SygusInst::needsCheck(Theory::Effort e)
{
  return e >= Theory::EFFORT_LAST_CALL;
}

QuantifiersModule::QEffort SygusInst::needsModel(Theory::Effort e)
{
  return QEFFORT_STANDARD;
}

void SygusInst::reset_round(Theory::Effort e)
{
  d_active_quant.clear();
  d_inactive_quant.clear();

  FirstOrderModel* model = d_quantEngine->getModel();
  uint32_t nasserted = model->getNumAssertedQuantifiers();

  for (uint32_t i = 0; i < nasserted; ++i)
  {
    Node q = model->getAssertedQuantifier(i);

    if (model->isQuantifierActive(q))
    {
      d_active_quant.insert(q);
      Node lit = getCeLiteral(q);

      bool value;
      if (d_quantEngine->getValuation().hasSatValue(lit, value))
      {
        if (!value)
        {
          if (!d_quantEngine->getValuation().isDecision(lit))
          {
            model->setQuantifierActive(q, false);
            d_active_quant.erase(q);
            d_inactive_quant.insert(q);
            Trace("sygus-inst") << "Set inactive: " << q << std::endl;
          }
        }
      }
    }
  }
}

void SygusInst::check(Theory::Effort e, QEffort quant_e)
{
  Trace("sygus-inst") << "Check " << e << ", " << quant_e << std::endl;

  if (quant_e != QEFFORT_STANDARD) return;

  FirstOrderModel* model = d_quantEngine->getModel();
  Instantiate* inst = d_quantEngine->getInstantiate();
  TermDbSygus* db = d_quantEngine->getTermDatabaseSygus();
  SygusExplain syexplain(db);
  NodeManager* nm = NodeManager::currentNM();

  for (const Node& q : d_active_quant)
  {
    std::vector<Node> terms;
    for (const Node& var : q[0])
    {
      Node dt_var = d_inst_constants[var];
      Node dt_eval = d_var_eval[var];
      Node value = model->getValue(dt_var);
      Node t = datatypes::utils::sygusToBuiltin(value);
      terms.push_back(t);

      std::vector<Node> exp;
      syexplain.getExplanationForEquality(dt_var, value, exp);
      Node lem;
      if (exp.empty())
      {
        lem = dt_eval.eqNode(t);
      }
      else
      {
        lem = nm->mkNode(kind::IMPLIES,
                         exp.size() == 1 ? exp[0] : nm->mkNode(kind::AND, exp),
                         dt_eval.eqNode(t));
      }

      if (d_lemma_cache.find(lem) == d_lemma_cache.end())
      {
        Trace("sygus-inst") << "Evaluation unfolding: " << lem << std::endl;
        d_quantEngine->addLemma(lem, false);
        d_lemma_cache.insert(lem);
      }
    }

    if (inst->addInstantiation(q, terms))
    {
      Trace("sygus-inst") << "Instantiate " << q << std::endl;
    }
  }
}

bool SygusInst::checkCompleteFor(Node q)
{
  return d_inactive_quant.find(q) != d_inactive_quant.end();
}

void SygusInst::registerQuantifier(Node q)
{
  Assert(d_ce_lemmas.find(q) == d_ce_lemmas.end());

  Trace("sygus-inst") << "Register " << q << std::endl;

  std::map<TypeNode, std::unordered_set<Node, NodeHashFunction>> extra_cons;
  std::map<TypeNode, std::unordered_set<Node, NodeHashFunction>> exclude_cons;
  std::map<TypeNode, std::unordered_set<Node, NodeHashFunction>> include_cons;
  std::unordered_set<Node, NodeHashFunction> term_irrelevant;

  /* Collect extra symbols in 'q' to be used in the grammar. */
  std::unordered_set<Node, NodeHashFunction> syms;
  expr::getSymbols(q, syms);
  for (const TNode& var : syms)
  {
    TypeNode tn = var.getType();
    extra_cons[tn].insert(var);
    Trace("sygus-inst") << "Found symbol: " << var << std::endl;
  }

  /* Construct grammar for each bound variable of 'q'. */
  Trace("sygus-inst") << "Process variables of " << q << std::endl;
  std::vector<TypeNode> types;
  for (const Node& var : q[0])
  {
    TypeNode tn = CegGrammarConstructor::mkSygusDefaultType(var.getType(),
                                                            Node(),
                                                            var.toString(),
                                                            extra_cons,
                                                            exclude_cons,
                                                            include_cons,
                                                            term_irrelevant);
    types.push_back(tn);

    Trace("sygus-inst") << "Construct (default) datatype for " << var
                        << std::endl
                        << tn << std::endl;
  }

  registerCeLemma(q, types);
}

/* Construct grammars for all bound variables of quantifier 'q'. Currently,
 * we use the default grammar of the variable's type.
 */
void SygusInst::preRegisterQuantifier(Node q)
{
  Trace("sygus-inst") << "preRegister " << q << std::endl;
  addCeLemma(q);
}

/*****************************************************************************/
/* private methods                                                           */
/*****************************************************************************/

Node SygusInst::getCeLiteral(Node q)
{
  auto it = d_ce_lits.find(q);
  if (it != d_ce_lits.end())
  {
    return it->second;
  }

  NodeManager* nm = NodeManager::currentNM();
  Node sk = nm->mkSkolem("CeLiteral", nm->booleanType());
  Node lit = d_quantEngine->getValuation().ensureLiteral(sk);
  d_ce_lits[q] = lit;
  return lit;
}

void SygusInst::registerCeLemma(Node q, std::vector<TypeNode>& types)
{
  Assert(q[0].getNumChildren() == types.size());
  Assert(d_ce_lemmas.find(q) == d_ce_lemmas.end());

  /* Generate counterexample lemma for 'q'. */
  NodeManager* nm = NodeManager::currentNM();
  TermDbSygus* db = d_quantEngine->getTermDatabaseSygus();

  /* For each variable x_i of \forall x_i . P[x_i], create a fresh datatype
   * instantiation constant ic_i with type types[i] and wrap each ic_i in
   * DT_SYGUS_EVAL(ic_i), which will be used to instantiate x_i. */
  std::vector<Node> vars;
  std::vector<Node> evals;
  for (size_t i = 0, size = types.size(); i < size; ++i)
  {
    TypeNode tn = types[i];
    TNode var = q[0][i];

    /* Create the instantiation constant and set attribute accordingly. */
    Node ic = nm->mkInstConstant(tn);
    InstConstantAttribute ica;
    ic.setAttribute(ica, q);

    db->registerEnumerator(ic, ic, nullptr, ROLE_ENUM_MULTI_SOLUTION);

    std::vector<Node> args = {ic};
    Node svl = tn.getDType().getSygusVarList();
    if (!svl.isNull())
    {
      args.insert(args.end(), svl.begin(), svl.end());
    }
    Node eval = nm->mkNode(kind::DT_SYGUS_EVAL, args);

    d_inst_constants.emplace(std::make_pair(var, ic));
    d_var_eval.emplace(std::make_pair(var, eval));

    vars.push_back(var);
    evals.push_back(eval);
  }

  Node lit = getCeLiteral(q);
  d_quantEngine->addRequirePhase(lit, true);

  /* The decision strategy for quantified formula 'q' ensures that its
   * counterexample literal is decided on first. It is user-context dependent.
   */
  Assert(d_dstrat.find(q) == d_dstrat.end());
  DecisionStrategy* ds =
      new DecisionStrategySingleton("CeLiteral",
                                    lit,
                                    d_quantEngine->getSatContext(),
                                    d_quantEngine->getValuation());

  d_dstrat[q].reset(ds);
  d_quantEngine->getDecisionManager()->registerStrategy(
      DecisionManager::STRAT_QUANT_CEGQI_FEASIBLE, ds);

  /* Add counterexample lemma (lit => ~P[x_i/eval_i]) */
  Node body =
      q[1].substitute(vars.begin(), vars.end(), evals.begin(), evals.end());
  Node lem = nm->mkNode(kind::OR, lit.negate(), body.negate());
  lem = Rewriter::rewrite(lem);

  d_ce_lemmas.emplace(std::make_pair(q, lem));
  Trace("sygus-inst") << "Register CE Lemma: " << lem << std::endl;
}

void SygusInst::addCeLemma(Node q)
{
  Assert(d_ce_lemmas.find(q) != d_ce_lemmas.end());

  /* Already added in previous contexts. */
  if (d_ce_lemma_added.find(q) != d_ce_lemma_added.end()) return;

  Node lem = d_ce_lemmas[q];
  d_quantEngine->addLemma(lem, false);
  d_ce_lemma_added.insert(q);
  Trace("sygus-inst") << "Add CE Lemma: " << lem << std::endl;
}

}  // namespace quantifiers
}  // namespace theory
}  // namespace CVC4
