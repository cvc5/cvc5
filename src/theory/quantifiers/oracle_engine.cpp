/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Oracle engine
 */

#include "theory/quantifiers/oracle_engine.h"

#include "expr/attribute.h"
#include "expr/skolem_manager.h"
#include "options/quantifiers_options.h"
#include "theory/quantifiers/first_order_model.h"
#include "theory/quantifiers/quantifiers_attributes.h"
#include "theory/quantifiers/quantifiers_inference_manager.h"
#include "theory/quantifiers/quantifiers_registry.h"
#include "theory/quantifiers/term_registry.h"
#include "theory/quantifiers/term_tuple_enumerator.h"
#include "theory/trust_substitutions.h"

using namespace cvc5::internal::kind;
using namespace cvc5::context;

namespace cvc5::internal {
namespace theory {
namespace quantifiers {

/** Attribute true for input variables */
struct OracleInputVarAttributeId
{
};
typedef expr::Attribute<OracleInputVarAttributeId, bool>
    OracleInputVarAttribute;
/** Attribute true for output variables */
struct OracleOutputVarAttributeId
{
};
typedef expr::Attribute<OracleOutputVarAttributeId, bool>
    OracleOutputVarAttribute;

OracleEngine::OracleEngine(Env& env,
                           QuantifiersState& qs,
                           QuantifiersInferenceManager& qim,
                           QuantifiersRegistry& qr,
                           TermRegistry& tr)
    : QuantifiersModule(env, qs, qim, qr, tr),
      d_oracleFuns(userContext()),
      d_ochecker(tr.getOracleChecker()),
      d_consistencyCheckPassed(false)
{
  Assert(d_ochecker != nullptr);
}

void OracleEngine::presolve() {
  // Ensure all oracle functions in top-level substitutions occur in
  // lemmas. Otherwise the oracles will not be invoked for those values
  // and the model will be inaccurate.
  std::unordered_map<Node, Node> subs =
      d_env.getTopLevelSubstitutions().get().getSubstitutions();
  std::unordered_set<Node> visited;
  std::vector<TNode> visit;
  for (const std::pair<const Node, Node>& s : subs)
  {
    visit.push_back(s.second);
  }
  TNode cur;
  while (!visit.empty())
  {
    cur = visit.back();
    visit.pop_back();
    if (visited.find(cur) == visited.end())
    {
      visited.insert(cur);
      if (OracleCaller::isOracleFunctionApp(cur))
      {
        SkolemManager* sm = NodeManager::currentNM()->getSkolemManager();
        Node k = sm->mkPurifySkolem(cur);
        Node eq = k.eqNode(cur);
        d_qim.lemma(eq, InferenceId::QUANTIFIERS_ORACLE_PURIFY_SUBS);
      }
      if (cur.getNumChildren() > 0)
      {
        visit.insert(visit.end(), cur.begin(), cur.end());
      }
    }
  }
}

bool OracleEngine::needsCheck(Theory::Effort e)
{
  return e == Theory::Effort::EFFORT_LAST_CALL;
}

// the model is built at this effort level
OracleEngine::QEffort OracleEngine::needsModel(Theory::Effort e)
{
  return QEFFORT_MODEL;
}

void OracleEngine::reset_round(Theory::Effort e)
{
  d_consistencyCheckPassed = false;
}

void OracleEngine::registerQuantifier(Node q) {}

void OracleEngine::check(Theory::Effort e, QEffort quant_e)
{
  if (quant_e != QEFFORT_MODEL)
  {
    return;
  }

  double clSet = 0;
  if (TraceIsOn("oracle-engine"))
  {
    clSet = double(clock()) / double(CLOCKS_PER_SEC);
    Trace("oracle-engine") << "---Oracle Engine Round, effort = " << e << "---"
                           << std::endl;
  }
  FirstOrderModel* fm = d_treg.getModel();
  TermDb* termDatabase = d_treg.getTermDatabase();
  NodeManager* nm = NodeManager::currentNM();
  unsigned nquant = fm->getNumAssertedQuantifiers();
  std::vector<Node> currInterfaces;
  for (unsigned i = 0; i < nquant; i++)
  {
    Node q = fm->getAssertedQuantifier(i);
    if (d_qreg.getOwner(q) != this)
    {
      continue;
    }
    currInterfaces.push_back(q);
  }
  // Note that we currently ignore oracle interface quantified formulas, and
  // look directly at the oracle functions. Note that:
  // (1) The lemmas with InferenceId QUANTIFIERS_ORACLE_INTERFACE are not
  // guarded by a quantified formula. This means that we are assuming that all
  // oracle interface quantified formulas are top-level assertions. This is
  // correct because we do not expose a way of embedding oracle interfaces into
  // formulas at the user level.
  // (2) We assume that oracle functions have associated oracle interface
  // quantified formulas that are in currInterfaces.
  // (3) We currently ignore oracle interface quantified formulas that are
  // not associated with oracle functions.
  //
  // The current design choices above are due to the fact that our support is
  // limited to "definitional SMTO" (see Polgreen et al 2022). In particular,
  // we only support oracles that define I/O equalities for oracle functions
  // only. The net effect of this class hence is to check the consistency of
  // oracle functions, and allow "sat" or otherwise add a lemma with id
  // QUANTIFIERS_ORACLE_INTERFACE.
  std::vector<Node> learnedLemmas;
  bool allFappsConsistent = true;
  // iterate over oracle functions
  for (const Node& f : d_oracleFuns)
  {
    TNodeTrie* tat = termDatabase->getTermArgTrie(f);
    if (!tat)
    {
      continue;
    }
    std::vector<Node> apps = tat->getLeaves(f.getType().getArgTypes().size());
    Trace("oracle-calls") << "Oracle fun " << f << " with " << apps.size()
                          << " applications." << std::endl;
    for (const auto& fapp : apps)
    {
      std::vector<Node> arguments;
      arguments.push_back(f);
      // evaluate arguments
      for (const auto& arg : fapp)
      {
        arguments.push_back(fm->getValue(arg));
      }
      // call oracle
      Node fappWithValues = nm->mkNode(APPLY_UF, arguments);
      Node predictedResponse = fm->getValue(fapp);
      if (!d_ochecker->checkConsistent(
              fappWithValues, predictedResponse, learnedLemmas))
      {
        allFappsConsistent = false;
      }
    }
  }
  // if all were consistent, we can terminate
  if (allFappsConsistent)
  {
    Trace("oracle-engine-state")
        << "All responses consistent, no lemmas added" << std::endl;
    d_consistencyCheckPassed = true;
  }
  else
  {
    for (const Node& l : learnedLemmas)
    {
      Trace("oracle-engine-state") << "adding lemma " << l << std::endl;
      d_qim.lemma(l, InferenceId::QUANTIFIERS_ORACLE_INTERFACE);
    }
  }
  // general SMTO: call constraint generators and assumption generators here

  if (TraceIsOn("oracle-engine"))
  {
    double clSet2 = double(clock()) / double(CLOCKS_PER_SEC);
    Trace("oracle-engine") << "Finished oracle engine, time = "
                           << (clSet2 - clSet) << std::endl;
  }
}

bool OracleEngine::checkCompleteFor(Node q)
{
  if (d_qreg.getOwner(q) != this)
  {
    return false;
  }
  // Only true if oracle consistency check was successful. Notice that
  // we can say true for *all* oracle interface quantified formulas in the
  // case that the consistency check passed. In particular, the invocation
  // of oracle interfaces does not need to be complete.
  return d_consistencyCheckPassed;
}

void OracleEngine::checkOwnership(Node q)
{
  // take ownership of quantified formulas that are oracle interfaces
  QuantAttributes& qa = d_qreg.getQuantAttributes();
  if (!qa.isOracleInterface(q))
  {
    return;
  }
  d_qreg.setOwner(q, this);
  // We expect oracle interfaces to be limited to definitional SMTO currently.
  if (Configuration::isAssertionBuild())
  {
    std::vector<Node> inputs, outputs;
    Node assume, constraint, oracle;
    if (!getOracleInterface(q, inputs, outputs, assume, constraint, oracle))
    {
      Assert(false) << "Not an oracle interface " << q;
    }
    else
    {
      Assert(outputs.size() == 1) << "Unhandled oracle constraint " << q;
      Assert(constraint.isConst() && constraint.getConst<bool>())
          << "Unhandled oracle constraint " << q;
    }
    CVC5_UNUSED bool isOracleFun = false;
    if (assume.getKind() == EQUAL)
    {
      for (size_t i = 0; i < 2; i++)
      {
        if (OracleCaller::isOracleFunctionApp(assume[i])
            && assume[1 - i] == outputs[0])
        {
          isOracleFun = true;
        }
      }
    }
    Assert(isOracleFun)
        << "Non-definitional oracle interface quantified formula " << q;
  }
}

std::string OracleEngine::identify() const
{
  return std::string("OracleEngine");
}

void OracleEngine::declareOracleFun(Node f) { d_oracleFuns.push_back(f); }

std::vector<Node> OracleEngine::getOracleFuns() const
{
  std::vector<Node> ofuns;
  for (const Node& f : d_oracleFuns)
  {
    ofuns.push_back(f);
  }
  return ofuns;
}

Node OracleEngine::mkOracleInterface(const std::vector<Node>& inputs,
                                     const std::vector<Node>& outputs,
                                     Node assume,
                                     Node constraint,
                                     Node oracleNode)
{
  Assert(!assume.isNull());
  Assert(!constraint.isNull());
  Assert(oracleNode.getKind() == ORACLE);
  NodeManager* nm = NodeManager::currentNM();
  Node ipl =
      nm->mkNode(INST_PATTERN_LIST, nm->mkNode(INST_ATTRIBUTE, oracleNode));
  std::vector<Node> vars;
  OracleInputVarAttribute oiva;
  for (Node v : inputs)
  {
    v.setAttribute(oiva, true);
    vars.push_back(v);
  }
  OracleOutputVarAttribute oova;
  for (Node v : outputs)
  {
    v.setAttribute(oova, true);
    vars.push_back(v);
  }
  Node bvl = nm->mkNode(BOUND_VAR_LIST, vars);
  Node body = nm->mkNode(ORACLE_FORMULA_GEN, assume, constraint);
  return nm->mkNode(FORALL, bvl, body, ipl);
}

bool OracleEngine::getOracleInterface(Node q,
                                      std::vector<Node>& inputs,
                                      std::vector<Node>& outputs,
                                      Node& assume,
                                      Node& constraint,
                                      Node& oracleNode) const
{
  QuantAttributes& qa = d_qreg.getQuantAttributes();
  if (qa.isOracleInterface(q))
  {
    // fill in data
    OracleInputVarAttribute oiva;
    for (const Node& v : q[0])
    {
      if (v.getAttribute(oiva))
      {
        inputs.push_back(v);
      }
      else
      {
        Assert(v.getAttribute(OracleOutputVarAttribute()));
        outputs.push_back(v);
      }
    }
    Assert(q[1].getKind() == ORACLE_FORMULA_GEN);
    assume = q[1][0];
    constraint = q[1][1];
    Assert(q.getNumChildren() == 3);
    Assert(q[2].getNumChildren() == 1);
    Assert(q[2][0].getNumChildren() == 1);
    Assert(q[2][0][0].getKind() == ORACLE);
    oracleNode = q[2][0][0];
    return true;
  }
  return false;
}

}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal
