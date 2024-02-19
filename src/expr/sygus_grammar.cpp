/******************************************************************************
 * Top contributors (to current version):
 *   Abdalrhman Mohamed, Andrew Reynolds
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

#include "expr/dtype.h"
#include "expr/skolem_manager.h"
#include "printer/printer.h"
#include "printer/smt2/smt2_printer.h"

namespace cvc5::internal {

SygusGrammar::SygusGrammar(const std::vector<Node>& sygusVars,
                           const std::vector<Node>& ntSyms)
    : d_sygusVars(sygusVars), d_ntSyms(ntSyms)
{
  for (const Node& ntSym : ntSyms)
  {
    d_rules.emplace(ntSym, std::vector<Node>{});
  }
}

void SygusGrammar::addRule(const Node& ntSym, const Node& rule)
{
  Assert(d_rules.find(ntSym) != d_rules.cend());
  Assert(rule.getType().isInstanceOf(ntSym.getType()));
  d_rules[ntSym].push_back(rule);
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
  Assert(d_rules.find(ntSym) != d_rules.cend());
  Assert(tn.isInstanceOf(ntSym.getType()));
  SkolemManager* sm = NodeManager::currentNM()->getSkolemManager();
  Node anyConst =
      sm->mkInternalSkolemFunction(InternalSkolemFunId::SYGUS_ANY_CONSTANT, tn);
  addRule(ntSym, anyConst);
}

void SygusGrammar::addAnyVariable(const Node& ntSym)
{
  Assert(d_rules.find(ntSym) != d_rules.cend());
  // each variable of appropriate type becomes a rule.
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

/**
 * Purify SyGuS grammar node.
 *
 * This returns a node where all occurrences of non-terminal symbols (those in
 * the domain of \p ntsToUnres) are replaced by fresh variables. For each
 * variable replaced in this way, we add the fresh variable it is replaced with
 * to \p args, and the unresolved types corresponding to the non-terminal symbol
 * to \p cargs (constructor args). In other words, \p args contains the free
 * variables in the node returned by this method (which should be bound by a
 * lambda), and \p cargs contains the types of the arguments of the sygus
 * constructor.
 *
 * @param n The node to purify.
 * @param args The free variables in the node returned by this method.
 * @param cargs The types of the arguments of the sygus constructor.
 * @param ntsToUnres Mapping from non-terminals to their unresolved types.
 * @return The purfied node.
 */
Node purifySygusGNode(const Node& n,
                      std::vector<Node>& args,
                      std::vector<TypeNode>& cargs,
                      const std::unordered_map<Node, TypeNode>& ntsToUnres)
{
  NodeManager* nm = NodeManager::currentNM();
  std::unordered_map<Node, TypeNode>::const_iterator itn = ntsToUnres.find(n);
  if (itn != ntsToUnres.cend())
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
    Node ptermc = purifySygusGNode(n[i], args, cargs, ntsToUnres);
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

bool isId(const Node& n)
{
  return n.getKind() == Kind::LAMBDA && n[0].getNumChildren() == 1
         && n[0][0] == n[1];
}

/**
 * Add \p rule to the set of constructors of \p dt.
 *
 * @param dt The datatype to which the rule is added.
 * @param rule The rule to add.
 * @param ntsToUnres Mapping from non-terminals to their unresolved types.
 */
void addSygusConstructor(DType& dt,
                         const Node& rule,
                         const std::unordered_map<Node, TypeNode>& ntsToUnres)
{
  NodeManager* nm = NodeManager::currentNM();
  SkolemManager* sm = nm->getSkolemManager();
  std::stringstream ss;
  if (rule.getKind() == Kind::SKOLEM
      && sm->getInternalId(rule) == InternalSkolemFunId::SYGUS_ANY_CONSTANT)
  {
    ss << dt.getName() << "_any_constant";
    dt.addSygusConstructor(rule, ss.str(), {rule.getType()}, 0);
  }
  else
  {
    std::vector<Node> args;
    std::vector<TypeNode> cargs;
    Node op = purifySygusGNode(rule, args, cargs, ntsToUnres);
    ss << op.getKind();
    if (!args.empty())
    {
      Node lbvl = nm->mkNode(Kind::BOUND_VAR_LIST, args);
      op = nm->mkNode(Kind::LAMBDA, lbvl, op);
    }
    // assign identity rules a weight of 0.
    dt.addSygusConstructor(op, ss.str(), cargs, isId(op) ? 0 : -1);
  }
}

TypeNode SygusGrammar::resolve(bool allowAny)
{
  if (!isResolved())
  {
    NodeManager* nm = NodeManager::currentNM();
    SkolemManager* sm = nm->getSkolemManager();
    Node bvl;
    if (!d_sygusVars.empty())
    {
      bvl = nm->mkNode(Kind::BOUND_VAR_LIST, d_sygusVars);
    }
    std::unordered_map<Node, TypeNode> ntsToUnres;
    for (const Node& ntSym : d_ntSyms)
    {
      // make the unresolved type, used for referencing the final version of
      // the ntSym's datatype
      ntsToUnres.emplace(ntSym, nm->mkUnresolvedDatatypeSort(ntSym.getName()));
    }
    // Set of non-terminals that can be arbitrary constants.
    std::unordered_set<Node> allowConsts;
    // push the rules into the sygus datatypes
    std::vector<DType> dts;
    for (const Node& ntSym : d_ntSyms)
    {
      // make the datatype, which encodes terms generated by this non-terminal
      DType dt(ntSym.getName());

      for (const Node& rule : d_rules[ntSym])
      {
        if (rule.getKind() == Kind::SKOLEM
            && sm->getInternalId(rule)
                   == InternalSkolemFunId::SYGUS_ANY_CONSTANT)
        {
          allowConsts.insert(ntSym);
        }
        addSygusConstructor(dt, rule, ntsToUnres);
      }
      bool allowConst = allowConsts.find(ntSym) != allowConsts.end();
      dt.setSygus(ntSym.getType(), bvl, allowConst || allowAny, allowAny);
      // We can be in a case where the only rule specified was (Variable T)
      // and there are no variables of type T, in which case this is a bogus
      // grammar. This results in the error below.
      Assert(dt.getNumConstructors() != 0) << "Grouped rule listing for " << dt
                                           << " produced an empty rule list";
      dts.push_back(dt);
    }
    d_datatype = nm->mkMutualDatatypeTypes(dts)[0];
  }
  // return the first datatype
  return d_datatype;
}

bool SygusGrammar::isResolved() { return !d_datatype.isNull(); }

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

}  // namespace cvc5::internal
