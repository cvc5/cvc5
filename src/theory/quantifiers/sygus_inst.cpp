/*********************                                                        */
/*! \file sygus_inst.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Mathias Preiner, Aina Niemetz, Andrew Reynolds
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
#include "theory/bv/theory_bv_utils.h"
#include "theory/datatypes/sygus_datatype_utils.h"
#include "theory/quantifiers/sygus/sygus_enumerator.h"
#include "theory/quantifiers/sygus/sygus_grammar_cons.h"
#include "theory/quantifiers/sygus/synth_engine.h"
#include "theory/quantifiers_engine.h"

namespace CVC4 {
namespace theory {
namespace quantifiers {

namespace {

/**
 * Collect maximal ground terms with type tn in node n.
 *
 * @param n: Node to traverse.
 * @param tn: Collects only terms with type tn.
 * @param terms: Collected terms.
 * @param cache: Caches visited nodes.
 * @param skip_quant: Do not traverse quantified formulas (skip quantifiers).
 */
void getMaxGroundTerms(TNode n,
                       TypeNode tn,
                       std::unordered_set<Node, NodeHashFunction>& terms,
                       std::unordered_set<TNode, TNodeHashFunction>& cache,
                       bool skip_quant = false)
{
  if (options::sygusInstTermSel() != options::SygusInstTermSelMode::MAX
      && options::sygusInstTermSel() != options::SygusInstTermSelMode::BOTH)
  {
    return;
  }

  Trace("sygus-inst-term") << "Find maximal terms with type " << tn
                           << " in: " << n << std::endl;

  Node cur;
  std::vector<TNode> visit;

  visit.push_back(n);
  do
  {
    cur = visit.back();
    visit.pop_back();

    if (cache.find(cur) != cache.end())
    {
      continue;
    }
    cache.insert(cur);

    if (expr::hasBoundVar(cur) || cur.getType() != tn)
    {
      if (!skip_quant || cur.getKind() != kind::FORALL)
      {
        visit.insert(visit.end(), cur.begin(), cur.end());
      }
    }
    else
    {
      terms.insert(cur);
      Trace("sygus-inst-term") << "  found: " << cur << std::endl;
    }
  } while (!visit.empty());
}

/*
 * Collect minimal ground terms with type tn in node n.
 *
 * @param n: Node to traverse.
 * @param tn: Collects only terms with type tn.
 * @param terms: Collected terms.
 * @param cache: Caches visited nodes and flags indicating whether a minimal
 *               term was already found in a subterm.
 * @param skip_quant: Do not traverse quantified formulas (skip quantifiers).
 */
void getMinGroundTerms(
    TNode n,
    TypeNode tn,
    std::unordered_set<Node, NodeHashFunction>& terms,
    std::unordered_map<TNode, std::pair<bool, bool>, TNodeHashFunction>& cache,
    bool skip_quant = false)
{
  if (options::sygusInstTermSel() != options::SygusInstTermSelMode::MIN
      && options::sygusInstTermSel() != options::SygusInstTermSelMode::BOTH)
  {
    return;
  }

  Trace("sygus-inst-term") << "Find minimal terms with type " << tn
                           << " in: " << n << std::endl;

  Node cur;
  std::vector<TNode> visit;

  visit.push_back(n);
  do
  {
    cur = visit.back();
    visit.pop_back();

    auto it = cache.find(cur);
    if (it == cache.end())
    {
      cache.emplace(cur, std::make_pair(false, false));
      if (!skip_quant || cur.getKind() != kind::FORALL)
      {
        visit.push_back(cur);
        visit.insert(visit.end(), cur.begin(), cur.end());
      }
    }
    /* up-traversal */
    else if (!it->second.first)
    {
      bool found_min_term = false;

      /* Check if we found a minimal term in one of the children. */
      for (const Node& c : cur)
      {
        found_min_term |= cache[c].second;
        if (found_min_term) break;
      }

      /* If we haven't found a minimal term yet, add this term if it has the
       * right type. */
      if (cur.getType() == tn && !expr::hasBoundVar(cur) && !found_min_term)
      {
        terms.insert(cur);
        found_min_term = true;
        Trace("sygus-inst-term") << "  found: " << cur << std::endl;
      }

      it->second.first = true;
      it->second.second = found_min_term;
    }
  } while (!visit.empty());
}

/*
 * Add special values for a given type.
 *
 * @param tn: The type node.
 * @param extra_cons: A map of TypeNode to constants, which are added in
 *                    addition to the default grammar.
 */
void addSpecialValues(
    const TypeNode& tn,
    std::map<TypeNode, std::unordered_set<Node, NodeHashFunction>>& extra_cons)
{
  if (tn.isBitVector())
  {
    uint32_t size = tn.getBitVectorSize();
    extra_cons[tn].insert(bv::utils::mkOnes(size));
    extra_cons[tn].insert(bv::utils::mkMinSigned(size));
    extra_cons[tn].insert(bv::utils::mkMaxSigned(size));
  }
}

}  // namespace

SygusInst::SygusInst(QuantifiersEngine* qe,
                     QuantifiersState& qs,
                     QuantifiersInferenceManager& qim)
    : QuantifiersModule(qs, qim, qe),
      d_ce_lemma_added(qs.getUserContext()),
      d_global_terms(qs.getUserContext()),
      d_notified_assertions(qs.getUserContext())
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
  options::SygusInstMode mode = options::sygusInstMode();

  for (const Node& q : d_active_quant)
  {
    const std::vector<Node>& inst_constants = d_inst_constants.at(q);
    const std::vector<Node>& dt_evals = d_var_eval.at(q);
    Assert(inst_constants.size() == dt_evals.size());
    Assert(inst_constants.size() == q[0].getNumChildren());

    std::vector<Node> terms, eval_unfold_lemmas;
    for (size_t i = 0, size = q[0].getNumChildren(); i < size; ++i)
    {
      Node dt_var = inst_constants[i];
      Node dt_eval = dt_evals[i];
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
      eval_unfold_lemmas.push_back(lem);
    }

    if (mode == options::SygusInstMode::PRIORITY_INST)
    {
      if (!inst->addInstantiation(q, terms))
      {
        sendEvalUnfoldLemmas(eval_unfold_lemmas);
      }
    }
    else if (mode == options::SygusInstMode::PRIORITY_EVAL)
    {
      if (!sendEvalUnfoldLemmas(eval_unfold_lemmas))
      {
        inst->addInstantiation(q, terms);
      }
    }
    else
    {
      Assert(mode == options::SygusInstMode::INTERLEAVE);
      inst->addInstantiation(q, terms);
      sendEvalUnfoldLemmas(eval_unfold_lemmas);
    }
  }
}

bool SygusInst::sendEvalUnfoldLemmas(const std::vector<Node>& lemmas)
{
  bool added_lemma = false;
  for (const Node& lem : lemmas)
  {
    Trace("sygus-inst") << "Evaluation unfolding: " << lem << std::endl;
    added_lemma |= d_quantEngine->addLemma(lem);
  }
  return added_lemma;
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

  /* Collect relevant local ground terms for each variable type. */
  if (options::sygusInstScope() == options::SygusInstScope::IN
      || options::sygusInstScope() == options::SygusInstScope::BOTH)
  {
    std::unordered_map<TypeNode,
                       std::unordered_set<Node, NodeHashFunction>,
                       TypeNodeHashFunction>
        relevant_terms;
    for (const Node& var : q[0])
    {
      TypeNode tn = var.getType();

      /* Collect relevant ground terms for type tn. */
      if (relevant_terms.find(tn) == relevant_terms.end())
      {
        std::unordered_set<Node, NodeHashFunction> terms;
        std::unordered_set<TNode, TNodeHashFunction> cache_max;
        std::unordered_map<TNode, std::pair<bool, bool>, TNodeHashFunction>
            cache_min;

        getMinGroundTerms(q, tn, terms, cache_min);
        getMaxGroundTerms(q, tn, terms, cache_max);
        relevant_terms.emplace(tn, terms);
      }

      /* Add relevant ground terms to grammar. */
      auto& terms = relevant_terms[tn];
      for (const auto& t : terms)
      {
        TypeNode ttn = t.getType();
        extra_cons[ttn].insert(t);
        Trace("sygus-inst") << "Adding (local) extra cons: " << t << std::endl;
      }
    }
  }

  /* Collect relevant global ground terms for each variable type. */
  if (options::sygusInstScope() == options::SygusInstScope::OUT
      || options::sygusInstScope() == options::SygusInstScope::BOTH)
  {
    for (const Node& var : q[0])
    {
      TypeNode tn = var.getType();

      /* Collect relevant ground terms for type tn. */
      if (d_global_terms.find(tn) == d_global_terms.end())
      {
        std::unordered_set<Node, NodeHashFunction> terms;
        std::unordered_set<TNode, TNodeHashFunction> cache_max;
        std::unordered_map<TNode, std::pair<bool, bool>, TNodeHashFunction>
            cache_min;

        for (const Node& a : d_notified_assertions)
        {
          getMinGroundTerms(a, tn, terms, cache_min, true);
          getMaxGroundTerms(a, tn, terms, cache_max, true);
        }
        d_global_terms.insert(tn, terms);
      }

      /* Add relevant ground terms to grammar. */
      auto it = d_global_terms.find(tn);
      if (it != d_global_terms.end())
      {
        for (const auto& t : (*it).second)
        {
          TypeNode ttn = t.getType();
          extra_cons[ttn].insert(t);
          Trace("sygus-inst")
              << "Adding (global) extra cons: " << t << std::endl;
        }
      }
    }
  }

  /* Construct grammar for each bound variable of 'q'. */
  Trace("sygus-inst") << "Process variables of " << q << std::endl;
  std::vector<TypeNode> types;
  for (const Node& var : q[0])
  {
    addSpecialValues(var.getType(), extra_cons);
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

void SygusInst::ppNotifyAssertions(const std::vector<Node>& assertions)
{
  for (const Node& a : assertions)
  {
    d_notified_assertions.insert(a);
  }
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
  Assert(d_inst_constants.find(q) == d_inst_constants.end());
  Assert(d_var_eval.find(q) == d_var_eval.end());

  Trace("sygus-inst") << "Register CE Lemma for " << q << std::endl;

  /* Generate counterexample lemma for 'q'. */
  NodeManager* nm = NodeManager::currentNM();
  TermDbSygus* db = d_quantEngine->getTermDatabaseSygus();

  /* For each variable x_i of \forall x_i . P[x_i], create a fresh datatype
   * instantiation constant ic_i with type types[i] and wrap each ic_i in
   * DT_SYGUS_EVAL(ic_i), which will be used to instantiate x_i. */
  std::vector<Node> evals;
  std::vector<Node> inst_constants;
  for (size_t i = 0, size = types.size(); i < size; ++i)
  {
    TypeNode tn = types[i];
    TNode var = q[0][i];

    /* Create the instantiation constant and set attribute accordingly. */
    Node ic = nm->mkInstConstant(tn);
    InstConstantAttribute ica;
    ic.setAttribute(ica, q);
    Trace("sygus-inst") << "Create " << ic << " for " << var << std::endl;

    db->registerEnumerator(ic, ic, nullptr, ROLE_ENUM_MULTI_SOLUTION);

    std::vector<Node> args = {ic};
    Node svl = tn.getDType().getSygusVarList();
    if (!svl.isNull())
    {
      args.insert(args.end(), svl.begin(), svl.end());
    }
    Node eval = nm->mkNode(kind::DT_SYGUS_EVAL, args);

    inst_constants.push_back(ic);
    evals.push_back(eval);
  }

  d_inst_constants.emplace(q, inst_constants);
  d_var_eval.emplace(q, evals);

  Node lit = getCeLiteral(q);
  d_quantEngine->addRequirePhase(lit, true);

  /* The decision strategy for quantified formula 'q' ensures that its
   * counterexample literal is decided on first. It is user-context dependent.
   */
  Assert(d_dstrat.find(q) == d_dstrat.end());
  DecisionStrategy* ds =
      new DecisionStrategySingleton("CeLiteral",
                                    lit,
                                    d_qstate.getSatContext(),
                                    d_quantEngine->getValuation());

  d_dstrat[q].reset(ds);
  d_quantEngine->getDecisionManager()->registerStrategy(
      DecisionManager::STRAT_QUANT_CEGQI_FEASIBLE, ds);

  /* Add counterexample lemma (lit => ~P[x_i/eval_i]) */
  Node body =
      q[1].substitute(q[0].begin(), q[0].end(), evals.begin(), evals.end());
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
