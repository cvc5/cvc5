/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Gereon Kremer, Morgan Deters
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * The quantifiers registry.
 */

#include "theory/quantifiers/quantifiers_registry.h"

#include "options/quantifiers_options.h"
#include "theory/quantifiers/quant_module.h"
#include "theory/quantifiers/term_util.h"

namespace cvc5::internal {
namespace theory {
namespace quantifiers {

QuantifiersRegistry::QuantifiersRegistry(Env& env)
    : QuantifiersUtil(env),
      d_quantAttr(),
      d_quantBoundInf(options().quantifiers.fmfTypeCompletionThresh,
                      options().quantifiers.finiteModelFind),
      d_quantPreproc(env)
{
}

void QuantifiersRegistry::registerQuantifier(Node q)
{
  if (d_inst_constants.find(q) != d_inst_constants.end())
  {
    return;
  }
  Assert(q.getKind() == kind::FORALL);
  NodeManager* nm = NodeManager::currentNM();
  Trace("quantifiers-engine")
      << "Instantiation constants for " << q << " : " << std::endl;
  for (size_t i = 0, nvars = q[0].getNumChildren(); i < nvars; i++)
  {
    d_vars[q].push_back(q[0][i]);
    // make instantiation constants
    Node ic = nm->mkInstConstant(q[0][i].getType());
    d_inst_constants_map[ic] = q;
    d_inst_constants[q].push_back(ic);
    Trace("quantifiers-engine") << "  " << ic << std::endl;
    // set the var number attribute
    InstVarNumAttribute ivna;
    ic.setAttribute(ivna, i);
    InstConstantAttribute ica;
    ic.setAttribute(ica, q);
  }
  // compute attributes
  d_quantAttr.computeAttributes(q);
}

bool QuantifiersRegistry::reset(Theory::Effort e) { return true; }

std::string QuantifiersRegistry::identify() const
{
  return "QuantifiersRegistry";
}

QuantifiersModule* QuantifiersRegistry::getOwner(Node q) const
{
  std::map<Node, QuantifiersModule*>::const_iterator it = d_owner.find(q);
  if (it == d_owner.end())
  {
    return nullptr;
  }
  return it->second;
}

void QuantifiersRegistry::setOwner(Node q,
                                   QuantifiersModule* m,
                                   int32_t priority)
{
  QuantifiersModule* mo = getOwner(q);
  if (mo == m)
  {
    return;
  }
  if (mo != nullptr)
  {
    if (priority <= d_owner_priority[q])
    {
      Trace("quant-warn") << "WARNING: setting owner of " << q << " to "
                          << (m ? m->identify() : "null")
                          << ", but already has owner " << mo->identify()
                          << " with higher priority!" << std::endl;
      return;
    }
  }
  d_owner[q] = m;
  d_owner_priority[q] = priority;
}

bool QuantifiersRegistry::hasOwnership(Node q, QuantifiersModule* m) const
{
  QuantifiersModule* mo = getOwner(q);
  return mo == m || mo == nullptr;
}

Node QuantifiersRegistry::getInstantiationConstant(Node q, size_t i) const
{
  std::map<Node, std::vector<Node> >::const_iterator it =
      d_inst_constants.find(q);
  if (it != d_inst_constants.end())
  {
    return it->second[i];
  }
  return Node::null();
}

size_t QuantifiersRegistry::getNumInstantiationConstants(Node q) const
{
  std::map<Node, std::vector<Node> >::const_iterator it =
      d_inst_constants.find(q);
  if (it != d_inst_constants.end())
  {
    return it->second.size();
  }
  return 0;
}

Node QuantifiersRegistry::getInstConstantBody(Node q)
{
  std::map<Node, Node>::const_iterator it = d_inst_const_body.find(q);
  if (it == d_inst_const_body.end())
  {
    Node n = substituteBoundVariablesToInstConstants(q[1], q);
    d_inst_const_body[q] = n;
    return n;
  }
  return it->second;
}

Node QuantifiersRegistry::substituteBoundVariablesToInstConstants(Node n,
                                                                  Node q)
{
  registerQuantifier(q);
  std::vector<Node>& vars = d_vars.at(q);
  std::vector<Node>& consts = d_inst_constants.at(q);
  Assert(vars.size() == q[0].getNumChildren());
  Assert(vars.size() == consts.size());
  return n.substitute(vars.begin(), vars.end(), consts.begin(), consts.end());
}

Node QuantifiersRegistry::substituteInstConstantsToBoundVariables(Node n,
                                                                  Node q)
{
  registerQuantifier(q);
  std::vector<Node>& vars = d_vars.at(q);
  std::vector<Node>& consts = d_inst_constants.at(q);
  Assert(vars.size() == q[0].getNumChildren());
  Assert(vars.size() == consts.size());
  return n.substitute(consts.begin(), consts.end(), vars.begin(), vars.end());
}

Node QuantifiersRegistry::substituteBoundVariables(
    Node n, Node q, const std::vector<Node>& terms)
{
  registerQuantifier(q);
  std::vector<Node>& vars = d_vars.at(q);
  Assert(vars.size() == q[0].getNumChildren());
  Assert(vars.size() == terms.size());
  return n.substitute(vars.begin(), vars.end(), terms.begin(), terms.end());
}

Node QuantifiersRegistry::substituteInstConstants(
    Node n, Node q, const std::vector<Node>& terms)
{
  registerQuantifier(q);
  std::vector<Node>& consts = d_inst_constants.at(q);
  Assert(consts.size() == q[0].getNumChildren());
  Assert(consts.size() == terms.size());
  return n.substitute(consts.begin(), consts.end(), terms.begin(), terms.end());
}

QuantAttributes& QuantifiersRegistry::getQuantAttributes()
{
  return d_quantAttr;
}

QuantifiersBoundInference& QuantifiersRegistry::getQuantifiersBoundInference()
{
  return d_quantBoundInf;
}
QuantifiersPreprocess& QuantifiersRegistry::getPreprocess()
{
  return d_quantPreproc;
}

Node QuantifiersRegistry::getNameForQuant(Node q) const
{
  Node name = d_quantAttr.getQuantName(q);
  if (!name.isNull())
  {
    return name;
  }
  return q;
}

bool QuantifiersRegistry::getNameForQuant(Node q, Node& name, bool req) const
{
  name = getNameForQuant(q);
  // if we have a name, or we did not require one
  return name != q || !req;
}

}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal
