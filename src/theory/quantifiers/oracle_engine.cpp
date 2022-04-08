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
 * Oracle engine
 */

#include "theory/quantifiers/oracle_engine.h"

#include "expr/skolem_manager.h"
#include "options/quantifiers_options.h"
#include "theory/quantifiers/first_order_model.h"
#include "theory/quantifiers/quantifiers_attributes.h"
#include "theory/quantifiers/quantifiers_inference_manager.h"
#include "theory/quantifiers/quantifiers_registry.h"
#include "theory/quantifiers/term_registry.h"
#include "theory/quantifiers/term_tuple_enumerator.h"

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
    : QuantifiersModule(env, qs, qim, qr, tr), d_oracleFuns(userContext())
{
}

void OracleEngine::presolve() {}

bool OracleEngine::needsCheck(Theory::Effort e)
{
  return e == Theory::Effort::EFFORT_LAST_CALL;
}

// the model is built at this effort level
OracleEngine::QEffort OracleEngine::needsModel(Theory::Effort e)
{
  return QEFFORT_MODEL;
}

void OracleEngine::reset_round(Theory::Effort e) {}

void OracleEngine::registerQuantifier(Node q) {}

void OracleEngine::check(Theory::Effort e, QEffort quant_e) {}

bool OracleEngine::checkCompleteFor(Node q) { return false; }

void OracleEngine::checkOwnership(Node q) {}

std::string OracleEngine::identify() const
{
  return std::string("OracleEngine");
}

void OracleEngine::declareOracleFun(Node f, const std::string& binName)
{
  OracleInterfaceAttribute oia;
  f.setAttribute(oia, binName);
  d_oracleFuns.push_back(f);
}

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
                                     const std::string& binName)
{
  Assert(!assume.isNull());
  Assert(!constraint.isNull());
  NodeManager* nm = NodeManager::currentNM();
  SkolemManager* sm = nm->getSkolemManager();
  OracleInterfaceAttribute oia;
  Node oiVar = sm->mkDummySkolem("oracle-interface", nm->booleanType());
  oiVar.setAttribute(oia, binName);
  Node ipl = nm->mkNode(INST_PATTERN_LIST, nm->mkNode(INST_ATTRIBUTE, oiVar));
  std::vector<Node> vars;
  OracleInputVarAttribute oiva;
  for (const Node& v : inputs)
  {
    v.setAttribute(oiva, true);
    vars.push_back(v);
  }
  OracleOutputVarAttribute oova;
  for (const Node& v : outputs)
  {
    v.setAttribute(oova, true);
    vars.push_back(v);
  }
  Node bvl = nm->mkNode(BOUND_VAR_LIST, vars);
  Node body = nm->mkNode(ORACLE_FORMULA_GEN, assume, constraint);
  return nm->mkNode(FORALL, bvl, body, ipl);
}

}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal
