/******************************************************************************
 * Top contributors (to current version):
 *   Abdalrhman Mohamed, Andrew Reynolds, Aina Niemetz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2024 by the authors listed in the file AUTHORS
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
#include "expr/dtype_cons.h"
#include "expr/skolem_manager.h"
#include "printer/printer.h"
#include "printer/smt2/smt2_printer.h"
#include "theory/datatypes/sygus_datatype_utils.h"

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

SygusGrammar::SygusGrammar(const std::vector<Node>& sygusVars,
                           const TypeNode& sdt)
    : d_sygusVars(sygusVars)
{
  Assert(sdt.isSygusDatatype());
  std::vector<TypeNode> tnlist;
  // ensure that sdt is first
  tnlist.push_back(sdt);
  std::map<TypeNode, Node> ntsyms;
  NodeManager* nm = NodeManager::currentNM();
  for (size_t i = 0; i < tnlist.size(); i++)
  {
    TypeNode tn = tnlist[i];
    Assert(tn.isSygusDatatype());
    const DType& dt = tn.getDType();
    std::stringstream ss;
    ss << dt.getName();
    Node v = nm->mkBoundVar(ss.str(), dt.getSygusType());
    ntsyms[tn] = v;
    d_ntSyms.push_back(v);
    d_rules.emplace(v, std::vector<Node>{});
    // process the subfield types
    std::unordered_set<TypeNode> tns = dt.getSubfieldTypes();
    for (const TypeNode& tnsc : tns)
    {
      if (tnsc.isSygusDatatype()
          && std::find(tnlist.begin(), tnlist.end(), tnsc) == tnlist.end())
      {
        tnlist.push_back(tnsc);
      }
    }
  }
  std::map<TypeNode, Node>::iterator itn;
  for (const TypeNode& tn : tnlist)
  {
    if (!tn.isSygusDatatype())
    {
      continue;
    }
    Node nts = ntsyms[tn];
    const DType& dt = tn.getDType();
    for (size_t i = 0, ncons = dt.getNumConstructors(); i < ncons; i++)
    {
      const DTypeConstructor& cons = dt[i];
      if (cons.isSygusAnyConstant())
      {
        addAnyConstant(nts, cons[0].getRangeType());
        continue;
      }
      Node op = cons.getSygusOp();
      std::vector<Node> args;
      for (size_t j = 0, nargs = cons.getNumArgs(); j < nargs; j++)
      {
        TypeNode argType = cons[j].getRangeType();
        itn = ntsyms.find(argType);
        Assert(itn != ntsyms.end()) << "Missing " << argType << " in " << op;
        args.push_back(itn->second);
      }
      Node rule = theory::datatypes::utils::mkSygusTerm(op, args, true);
      addRule(nts, rule);
    }
  }
}

void SygusGrammar::addRule(const Node& ntSym, const Node& rule)
{
  Assert(d_rules.find(ntSym) != d_rules.cend());
  Assert(rule.getType().isInstanceOf(ntSym.getType()));
  // avoid duplication
  std::vector<Node>& rs = d_rules[ntSym];
  if (std::find(rs.begin(), rs.end(), rule) == rs.end())
  {
    rs.push_back(rule);
  }
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
      sm->mkInternalSkolemFunction(InternalSkolemId::SYGUS_ANY_CONSTANT, tn);
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
 * @param ntSymMap Map from each variable in args to the non-terminal they were
 * introduced for.
 * @param nts The list of non-terminal symbols
 * @return The purfied node.
 */
Node purifySygusGNode(const Node& n,
                      std::vector<Node>& args,
                      std::map<Node, Node>& ntSymMap,
                      const std::vector<Node>& nts)
{
  NodeManager* nm = NodeManager::currentNM();
  // if n is non-terminal
  if (std::find(nts.begin(), nts.end(), n) != nts.end())
  {
    Node ret = nm->mkBoundVar(n.getType());
    ntSymMap[ret] = n;
    args.push_back(ret);
    return ret;
  }
  std::vector<Node> pchildren;
  bool childChanged = false;
  for (size_t i = 0, nchild = n.getNumChildren(); i < nchild; i++)
  {
    Node ptermc = purifySygusGNode(n[i], args, ntSymMap, nts);
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
                         const std::vector<Node>& nts,
                         const std::unordered_map<Node, TypeNode>& ntsToUnres)
{
  NodeManager* nm = NodeManager::currentNM();
  SkolemManager* sm = nm->getSkolemManager();
  std::stringstream ss;
  if (rule.getKind() == Kind::SKOLEM
      && sm->getInternalId(rule) == InternalSkolemId::SYGUS_ANY_CONSTANT)
  {
    ss << dt.getName() << "_any_constant";
    dt.addSygusConstructor(rule, ss.str(), {rule.getType()}, 0);
  }
  else
  {
    std::vector<Node> args;
    std::map<Node, Node> ntSymMap;
    Node op = purifySygusGNode(rule, args, ntSymMap, nts);
    std::vector<TypeNode> cargs;
    std::unordered_map<Node, TypeNode>::const_iterator it;
    for (const Node& a : args)
    {
      Assert(ntSymMap.find(a) != ntSymMap.end());
      Node na = ntSymMap[a];
      it = ntsToUnres.find(na);
      Assert(it != ntsToUnres.end());
      cargs.push_back(it->second);
    }
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

Node SygusGrammar::getLambdaForRule(const Node& r,
                                    std::map<Node, Node>& ntSymMap) const
{
  std::vector<Node> args;
  Node rp = purifySygusGNode(r, args, ntSymMap, d_ntSyms);
  if (!args.empty())
  {
    NodeManager* nm = NodeManager::currentNM();
    return nm->mkNode(Kind::LAMBDA, nm->mkNode(Kind::BOUND_VAR_LIST, args), rp);
  }
  return r;
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
            && sm->getInternalId(rule) == InternalSkolemId::SYGUS_ANY_CONSTANT)
        {
          allowConsts.insert(ntSym);
        }
        addSygusConstructor(dt, rule, d_ntSyms, ntsToUnres);
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
