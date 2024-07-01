/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Aina Niemetz, Mathias Preiner
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2024 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Generic sygus utilities.
 */

#include "theory/quantifiers/sygus/sygus_utils.h"

#include <sstream>

#include "expr/node_algorithm.h"
#include "expr/skolem_manager.h"
#include "theory/datatypes/sygus_datatype_utils.h"
#include "theory/quantifiers/quantifiers_attributes.h"

using namespace cvc5::internal::kind;

namespace cvc5::internal {
namespace theory {
namespace quantifiers {

/**
 * Attribute for specifying a solution for a function-to-synthesize. This is
 * used for marking certain functions that we have solved for, e.g. during
 * preprocessing.
 */
struct SygusSolutionAttributeId
{
};
typedef expr::Attribute<SygusSolutionAttributeId, Node> SygusSolutionAttribute;

/**
 * Attribute for associating a function-to-synthesize with a first order
 * variable whose type is a sygus datatype type that encodes its grammar.
 */
struct SygusSynthGrammarAttributeId
{
};
typedef expr::Attribute<SygusSynthGrammarAttributeId, Node>
    SygusSynthGrammarAttribute;

/**
 * Attribute for associating a function-to-synthesize with its formal argument
 * list.
 */
struct SygusSynthFunVarListAttributeId
{
};
typedef expr::Attribute<SygusSynthFunVarListAttributeId, Node>
    SygusSynthFunVarListAttribute;

Node SygusUtils::mkSygusConjecture(const std::vector<Node>& fs,
                                   Node conj,
                                   const std::vector<Node>& iattrs)
{
  Assert(!fs.empty());
  NodeManager* nm = NodeManager::currentNM();
  SkolemManager* sm = nm->getSkolemManager();
  SygusAttribute ca;
  Node sygusVar = sm->mkDummySkolem("sygus", nm->booleanType());
  sygusVar.setAttribute(ca, true);
  std::vector<Node> ipls{nm->mkNode(Kind::INST_ATTRIBUTE, sygusVar)};
  // insert the remaining instantiation attributes
  ipls.insert(ipls.end(), iattrs.begin(), iattrs.end());
  Node ipl = nm->mkNode(Kind::INST_PATTERN_LIST, ipls);
  Node bvl = nm->mkNode(Kind::BOUND_VAR_LIST, fs);
  return nm->mkNode(Kind::FORALL, bvl, conj, ipl);
}

Node SygusUtils::mkSygusConjecture(const std::vector<Node>& fs, Node conj)
{
  std::vector<Node> iattrs;
  return mkSygusConjecture(fs, conj, iattrs);
}

Node SygusUtils::mkSygusConjecture(const std::vector<Node>& fs,
                                   Node conj,
                                   const Subs& solvedf)
{
  Assert(!fs.empty());
  NodeManager* nm = NodeManager::currentNM();
  SkolemManager* sm = nm->getSkolemManager();
  std::vector<Node> iattrs;
  // take existing properties, without the previous solves
  SygusSolutionAttribute ssa;
  // add the current solves, which should be a superset of the previous ones
  for (size_t i = 0, nsolved = solvedf.size(); i < nsolved; i++)
  {
    Node eq = solvedf.getEquality(i);
    Node var = sm->mkDummySkolem("solved", nm->booleanType());
    var.setAttribute(ssa, eq);
    Node ipv = nm->mkNode(Kind::INST_ATTRIBUTE, var);
    iattrs.push_back(ipv);
  }
  return mkSygusConjecture(fs, conj, iattrs);
}

void SygusUtils::decomposeSygusConjecture(Node q,
                                          std::vector<Node>& fs,
                                          std::vector<Node>& unsf,
                                          Subs& solvedf)
{
  Assert(q.getKind() == Kind::FORALL);
  Assert(q.getNumChildren() == 3);
  Node ipl = q[2];
  Assert(ipl.getKind() == Kind::INST_PATTERN_LIST);
  fs.insert(fs.end(), q[0].begin(), q[0].end());
  SygusSolutionAttribute ssa;
  for (const Node& ip : ipl)
  {
    if (ip.getKind() == Kind::INST_ATTRIBUTE)
    {
      Node ipv = ip[0];
      // does it specify a sygus solution?
      if (ipv.hasAttribute(ssa))
      {
        Node eq = ipv.getAttribute(ssa);
        Assert(std::find(fs.begin(), fs.end(), eq[0]) != fs.end());
        solvedf.addEquality(eq);
      }
    }
  }
  // add to unsolved functions
  for (const Node& f : fs)
  {
    if (!solvedf.contains(f))
    {
      unsf.push_back(f);
    }
  }
}

Node SygusUtils::decomposeSygusBody(Node conj, std::vector<Node>& vs)
{
  if (conj.getKind() == Kind::NOT && conj[0].getKind() == Kind::FORALL)
  {
    vs.insert(vs.end(), conj[0][0].begin(), conj[0][0].end());
    return conj[0][1].negate();
  }
  return conj;
}

void SygusUtils::setSygusArgumentList(Node f, const Node& bvl)
{
  if (!bvl.isNull())
  {
    // use an attribute to mark its bound variable list
    SygusSynthFunVarListAttribute ssfvla;
    f.setAttribute(ssfvla, bvl);
  }
}

Node SygusUtils::getOrMkSygusArgumentList(Node f)
{
  Node sfvl = f.getAttribute(SygusSynthFunVarListAttribute());
  if (sfvl.isNull() && f.getType().isFunction())
  {
    NodeManager* nm = NodeManager::currentNM();
    std::vector<TypeNode> argTypes = f.getType().getArgTypes();
    // make default variable list if none was specified by input
    std::vector<Node> bvs;
    for (unsigned j = 0, size = argTypes.size(); j < size; j++)
    {
      std::stringstream ss;
      ss << "arg" << j;
      bvs.push_back(nm->mkBoundVar(ss.str(), argTypes[j]));
    }
    sfvl = nm->mkNode(Kind::BOUND_VAR_LIST, bvs);
    f.setAttribute(SygusSynthFunVarListAttribute(), sfvl);
  }
  return sfvl;
}

void SygusUtils::getOrMkSygusArgumentList(Node f, std::vector<Node>& formals)
{
  Node sfvl = getOrMkSygusArgumentList(f);
  if (!sfvl.isNull())
  {
    formals.insert(formals.end(), sfvl.begin(), sfvl.end());
  }
}

Node SygusUtils::wrapSolution(Node f, Node sol)
{
  Node al = getOrMkSygusArgumentList(f);
  if (!al.isNull())
  {
    sol = NodeManager::currentNM()->mkNode(Kind::LAMBDA, al, sol);
  }
  Assert(!expr::hasFreeVar(sol));
  return sol;
}

void SygusUtils::setSygusType(Node f, const TypeNode& tn)
{
  Assert(!tn.isNull());
  Assert(getSygusType(f).isNull());
  Node sym = NodeManager::currentNM()->mkBoundVar("sfproxy", tn);
  // use an attribute to mark its grammar
  SygusSynthGrammarAttribute ssfga;
  f.setAttribute(ssfga, sym);
}

TypeNode SygusUtils::getSygusType(const Node& f)
{
  Node gv = f.getAttribute(SygusSynthGrammarAttribute());
  if (!gv.isNull())
  {
    return gv.getType();
  }
  return TypeNode::null();
}

Node SygusUtils::mkSygusTermFor(const Node& f)
{
  NodeManager* nm = NodeManager::currentNM();
  TypeNode tn = getSygusType(f);
  Node bvl = getOrMkSygusArgumentList(f);
  if (tn.isNull())
  {
    Node ret;
    if (f.getType().isFunction())
    {
      Assert(!bvl.isNull());
      ret = nm->mkGroundValue(f.getType().getRangeType());
      // give the appropriate variable list
      ret = nm->mkNode(Kind::LAMBDA, bvl, ret);
    }
    else
    {
      ret = nm->mkGroundValue(f.getType());
    }
    return ret;
  }
  Node ret = nm->mkGroundValue(tn);
  // use external=true
  ret = datatypes::utils::sygusToBuiltin(ret, true);
  if (!bvl.isNull())
  {
    ret = nm->mkNode(Kind::LAMBDA, bvl, ret);
  }
  return ret;
}

}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal
