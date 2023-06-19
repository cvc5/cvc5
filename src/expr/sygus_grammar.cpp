/******************************************************************************
 * Top contributors (to current version):
 *   Abdalrhman Mohamed
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Implementation of class for constructing SyGuS Grammars.
 */

#include "expr/sygus_grammar.h"

#include <sstream>

#include "expr/skolem_manager.h"
#include "printer/printer.h"
#include "printer/smt2/smt2_printer.h"

namespace cvc5::internal {

SygusGrammar::SygusGrammar(const std::vector<Node>& sygusVars,
                           const std::vector<Node>& ntSyms)
    : d_sygusVars(sygusVars), d_ntSyms(ntSyms)
{
  NodeManager* nm = NodeManager::currentNM();
  for (const Node& ntSym : ntSyms)
  {
    std::vector<Node> emptyVec;
    d_rules.emplace(ntSym, emptyVec);
    d_sdts.emplace(ntSym, SygusDatatype(ntSym.getName()));
    d_ntsToUnres.emplace(ntSym, nm->mkUnresolvedDatatypeSort(ntSym.getName()));
  }
}

bool isId(const Node& n)
{
  return n.getKind() == kind::LAMBDA && n[0].getNumChildren() == 1
         && n[0][0] == n[1];
}

void SygusGrammar::addRule(const Node& ntSym, const Node& rule)
{
  Assert(d_sdts.find(ntSym) != d_sdts.cend());
  Assert(rule.getType().isInstanceOf(ntSym.getType()));
  d_rules[ntSym].push_back(rule);
}

void SygusGrammar::addRuleInternal(const Node& ntSym, const Node& rule)
{
  NodeManager* nm = NodeManager::currentNM();
  std::vector<Node> args;
  std::vector<TypeNode> cargs;
  Node op = purifySygusGNode(rule, args, cargs);
  std::stringstream ss;
  ss << op.getKind();
  if (!args.empty())
  {
    Node lbvl = nm->mkNode(kind::BOUND_VAR_LIST, args);
    op = nm->mkNode(kind::LAMBDA, lbvl, op);
  }
  // assign identity rules a weight of 0.
  d_sdts.at(ntSym).addConstructor(op, ss.str(), cargs, isId(op) ? 0 : -1);
}

void SygusGrammar::addRules(const Node& ntSym, const std::vector<Node>& rules)
{
  for (const Node& rule : rules)
  {
    addRule(ntSym, rule);
  }
}

void SygusGrammar::addAnyConstant(const Node& ntSym, const TypeNode& tn)
{
  Assert(d_sdts.find(ntSym) != d_sdts.cend());
  Assert(tn.isInstanceOf(ntSym.getType()));
  SkolemManager* sm = NodeManager::currentNM()->getSkolemManager();
  Node anyConst = sm->mkSkolemFunction(SkolemFunId::SYGUS_ANY_CONSTANT, tn);
  addRule(ntSym, anyConst);
}

void SygusGrammar::addAnyVariable(const Node& ntSym)
{
  Assert(d_sdts.find(ntSym) != d_sdts.cend());
  // each variable of appropriate type becomes a sygus constructor in sdt.
  for (const Node& v : d_sygusVars)
  {
    if (v.getType().isInstanceOf(ntSym.getType()))
    {
      addRule(ntSym, v);
    }
  }
}

void SygusGrammar::removeRule(const Node& ntSym, const Node& rule)
{
  std::unordered_map<Node, std::vector<Node>>::iterator itr =
      d_rules.find(ntSym);
  Assert(itr != d_rules.end());
  std::vector<Node>::iterator it =
      std::find(itr->second.begin(), itr->second.end(), rule);
  Assert(it != itr->second.end());
  itr->second.erase(it);
}

TypeNode SygusGrammar::resolve(bool allowAny)
{
  if (!isResolved())
  {
    NodeManager* nm = NodeManager::currentNM();
    SkolemManager* sm = nm->getSkolemManager();
    // Set of non-terminals that can be arbitrary constants.
    std::unordered_set<Node> allowConsts;
    // push the rules into the sygus datatypes
    for (const std::pair<const Node, std::vector<Node>>& g : d_rules)
    {
      for (const Node& r : g.second)
      {
        if (r.getKind() == kind::SKOLEM
            && sm->getId(r) == SkolemFunId::SYGUS_ANY_CONSTANT)
        {
          allowConsts.insert(g.first);
          d_sdts.at(g.first).addAnyConstantConstructor(r.getType());
        }
        else
        {
          addRuleInternal(g.first, r);
        }
      }
    }
    Node bvl;
    if (!d_sygusVars.empty())
    {
      bvl = nm->mkNode(kind::BOUND_VAR_LIST, d_sygusVars);
    }
    std::vector<DType> datatypes;
    for (const Node& ntSym : d_ntSyms)
    {
      bool allowConst = allowConsts.find(ntSym) != allowConsts.cend();
      d_sdts.at(ntSym).initializeDatatype(
          ntSym.getType(), bvl, allowConst || allowAny, allowAny);
      datatypes.push_back(d_sdts.at(ntSym).getDatatype());
    }
    d_datatype = nm->mkMutualDatatypeTypes(datatypes)[0];
  }
  // return the first datatype
  return d_datatype;
}

bool SygusGrammar::isResolved()
{
  return !d_datatype.isNull();
}

const std::vector<Node>& SygusGrammar::getSygusVars() const
{
  return d_sygusVars;
}

const std::vector<Node>& SygusGrammar::getNtSyms() const { return d_ntSyms; }

const std::vector<Node>& SygusGrammar::getRulesFor(const Node& ntSym) const
{
  std::unordered_map<Node, std::vector<Node>>::const_iterator itr =
      d_rules.find(ntSym);
  Assert(itr != d_rules.end());
  return itr->second;
}

std::string SygusGrammar::toString() const
{
  std::stringstream ss;
  // clone this grammar before printing it to avoid freezing it.
  return printer::smt2::Smt2Printer::sygusGrammarString(
      SygusGrammar(*this).resolve());
}

Node SygusGrammar::purifySygusGNode(const Node& n,
                                    std::vector<Node>& args,
                                    std::vector<TypeNode>& cargs) const
{
  NodeManager* nm = NodeManager::currentNM();
  std::unordered_map<Node, TypeNode>::const_iterator itn = d_ntsToUnres.find(n);
  if (itn != d_ntsToUnres.cend())
  {
    Node ret = nm->mkBoundVar(n.getType());
    args.push_back(ret);
    cargs.push_back(itn->second);
    return ret;
  }
  std::vector<Node> pchildren;
  bool childChanged = false;
  for (size_t i = 0, nchild = n.getNumChildren(); i < nchild; i++)
  {
    Node ptermc = purifySygusGNode(n[i], args, cargs);
    pchildren.push_back(ptermc);
    childChanged = childChanged || ptermc != n[i];
  }
  if (!childChanged)
  {
    return n;
  }
  internal::Node nret;
  if (n.getMetaKind() == kind::metakind::PARAMETERIZED)
  {
    // it's an indexed operator so we should provide the op
    internal::NodeBuilder nb(n.getKind());
    nb << n.getOperator();
    nb.append(pchildren);
    nret = nb.constructNode();
  }
  else
  {
    nret = nm->mkNode(n.getKind(), pchildren);
  }
  return nret;
}

}  // namespace cvc5::internal
