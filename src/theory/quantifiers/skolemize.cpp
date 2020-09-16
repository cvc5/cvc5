/*********************                                                        */
/*! \file skolemize.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Implementation of skolemization utility
 **/

#include "theory/quantifiers/skolemize.h"

#include "options/quantifiers_options.h"
#include "theory/quantifiers/quantifiers_attributes.h"
#include "theory/quantifiers/term_util.h"
#include "theory/quantifiers_engine.h"
#include "theory/sort_inference.h"
#include "theory/theory_engine.h"

using namespace CVC4::kind;

namespace CVC4 {
namespace theory {
namespace quantifiers {

Skolemize::Skolemize(QuantifiersEngine* qe, context::UserContext* u)
    : d_quantEngine(qe), d_skolemized(u)
{
}

Node Skolemize::process(Node q)
{
  // do skolemization
  if (d_skolemized.find(q) == d_skolemized.end())
  {
    Node body = getSkolemizedBody(q);
    NodeBuilder<> nb(kind::OR);
    nb << q << body.notNode();
    Node lem = nb;
    d_skolemized[q] = lem;
    return lem;
  }
  return Node::null();
}

bool Skolemize::getSkolemConstants(Node q, std::vector<Node>& skolems)
{
  std::unordered_map<Node, std::vector<Node>, NodeHashFunction>::iterator it =
      d_skolem_constants.find(q);
  if (it != d_skolem_constants.end())
  {
    skolems.insert(skolems.end(), it->second.begin(), it->second.end());
    return true;
  }
  return false;
}

Node Skolemize::getSkolemConstant(Node q, unsigned i)
{
  std::unordered_map<Node, std::vector<Node>, NodeHashFunction>::iterator it =
      d_skolem_constants.find(q);
  if (it != d_skolem_constants.end())
  {
    if (i < it->second.size())
    {
      return it->second[i];
    }
  }
  return Node::null();
}

void Skolemize::getSelfSel(const DType& dt,
                           const DTypeConstructor& dc,
                           Node n,
                           TypeNode ntn,
                           std::vector<Node>& selfSel)
{
  TypeNode tspec;
  if (dt.isParametric())
  {
    tspec = dc.getSpecializedConstructorType(n.getType());
    Trace("sk-ind-debug") << "Specialized constructor type : " << tspec
                          << std::endl;
    Assert(tspec.getNumChildren() == dc.getNumArgs());
  }
  Trace("sk-ind-debug") << "Check self sel " << dc.getName() << " "
                        << dt.getName() << std::endl;
  NodeManager* nm = NodeManager::currentNM();
  for (unsigned j = 0; j < dc.getNumArgs(); j++)
  {
    std::vector<Node> ssc;
    if (dt.isParametric())
    {
      Trace("sk-ind-debug") << "Compare " << tspec[j] << " " << ntn
                            << std::endl;
      if (tspec[j] == ntn)
      {
        ssc.push_back(n);
      }
    }
    else
    {
      TypeNode tn = dc[j].getRangeType();
      Trace("sk-ind-debug") << "Compare " << tn << " " << ntn << std::endl;
      if (tn == ntn)
      {
        ssc.push_back(n);
      }
    }
    for (unsigned k = 0; k < ssc.size(); k++)
    {
      Node ss = nm->mkNode(
          APPLY_SELECTOR_TOTAL, dc.getSelectorInternal(n.getType(), j), n);
      if (std::find(selfSel.begin(), selfSel.end(), ss) == selfSel.end())
      {
        selfSel.push_back(ss);
      }
    }
  }
}

Node Skolemize::mkSkolemizedBody(Node f,
                                 Node n,
                                 std::vector<TypeNode>& argTypes,
                                 std::vector<TNode>& fvs,
                                 std::vector<Node>& sk,
                                 Node& sub,
                                 std::vector<unsigned>& sub_vars)
{
  NodeManager* nm = NodeManager::currentNM();
  Assert(sk.empty() || sk.size() == f[0].getNumChildren());
  // calculate the variables and substitution
  std::vector<TNode> ind_vars;
  std::vector<unsigned> ind_var_indicies;
  std::vector<TNode> vars;
  std::vector<unsigned> var_indicies;
  for (unsigned i = 0; i < f[0].getNumChildren(); i++)
  {
    if (isInductionTerm(f[0][i]))
    {
      ind_vars.push_back(f[0][i]);
      ind_var_indicies.push_back(i);
    }
    else
    {
      vars.push_back(f[0][i]);
      var_indicies.push_back(i);
    }
    Node s;
    // make the new function symbol or use existing
    if (i >= sk.size())
    {
      if (argTypes.empty())
      {
        s = NodeManager::currentNM()->mkSkolem(
            "skv", f[0][i].getType(), "created during skolemization");
      }
      else
      {
        TypeNode typ = NodeManager::currentNM()->mkFunctionType(
            argTypes, f[0][i].getType());
        Node op = NodeManager::currentNM()->mkSkolem(
            "skop", typ, "op created during pre-skolemization");
        // DOTHIS: set attribute on op, marking that it should not be selected
        // as trigger
        std::vector<Node> funcArgs;
        funcArgs.push_back(op);
        funcArgs.insert(funcArgs.end(), fvs.begin(), fvs.end());
        s = NodeManager::currentNM()->mkNode(kind::APPLY_UF, funcArgs);
      }
      sk.push_back(s);
    }
    else
    {
      Assert(sk[i].getType() == f[0][i].getType());
    }
  }
  Node ret;
  if (vars.empty())
  {
    ret = n;
  }
  else
  {
    std::vector<Node> var_sk;
    for (unsigned i = 0; i < var_indicies.size(); i++)
    {
      var_sk.push_back(sk[var_indicies[i]]);
    }
    Assert(vars.size() == var_sk.size());
    ret = n.substitute(vars.begin(), vars.end(), var_sk.begin(), var_sk.end());
  }
  if (!ind_vars.empty())
  {
    Trace("sk-ind") << "Ind strengthen : (not " << f << ")" << std::endl;
    Trace("sk-ind") << "Skolemized is : " << ret << std::endl;
    Node n_str_ind;
    TypeNode tn = ind_vars[0].getType();
    Node k = sk[ind_var_indicies[0]];
    Node nret = ret.substitute(ind_vars[0], k);
    // note : everything is under a negation
    // the following constructs ~( R( x, k ) => ~P( x ) )
    if (options::dtStcInduction() && tn.isDatatype())
    {
      const DType& dt = tn.getDType();
      std::vector<Node> disj;
      for (unsigned i = 0; i < dt.getNumConstructors(); i++)
      {
        std::vector<Node> selfSel;
        getSelfSel(dt, dt[i], k, tn, selfSel);
        std::vector<Node> conj;
        conj.push_back(nm->mkNode(APPLY_TESTER, dt[i].getTester(), k).negate());
        for (unsigned j = 0; j < selfSel.size(); j++)
        {
          conj.push_back(ret.substitute(ind_vars[0], selfSel[j]).negate());
        }
        disj.push_back(conj.size() == 1
                           ? conj[0]
                           : NodeManager::currentNM()->mkNode(OR, conj));
      }
      Assert(!disj.empty());
      n_str_ind = disj.size() == 1
                      ? disj[0]
                      : NodeManager::currentNM()->mkNode(AND, disj);
    }
    else if (options::intWfInduction() && tn.isInteger())
    {
      Node icond = NodeManager::currentNM()->mkNode(
          GEQ, k, NodeManager::currentNM()->mkConst(Rational(0)));
      Node iret =
          ret.substitute(
                 ind_vars[0],
                 NodeManager::currentNM()->mkNode(
                     MINUS, k, NodeManager::currentNM()->mkConst(Rational(1))))
              .negate();
      n_str_ind = NodeManager::currentNM()->mkNode(OR, icond.negate(), iret);
      n_str_ind = NodeManager::currentNM()->mkNode(AND, icond, n_str_ind);
    }
    else
    {
      Trace("sk-ind") << "Unknown induction for term : " << ind_vars[0]
                      << ", type = " << tn << std::endl;
      Assert(false);
    }
    Trace("sk-ind") << "Strengthening is : " << n_str_ind << std::endl;

    std::vector<Node> rem_ind_vars;
    rem_ind_vars.insert(
        rem_ind_vars.end(), ind_vars.begin() + 1, ind_vars.end());
    if (!rem_ind_vars.empty())
    {
      Node bvl = NodeManager::currentNM()->mkNode(BOUND_VAR_LIST, rem_ind_vars);
      nret = NodeManager::currentNM()->mkNode(FORALL, bvl, nret);
      nret = Rewriter::rewrite(nret);
      sub = nret;
      sub_vars.insert(
          sub_vars.end(), ind_var_indicies.begin() + 1, ind_var_indicies.end());
      n_str_ind = NodeManager::currentNM()
                      ->mkNode(FORALL, bvl, n_str_ind.negate())
                      .negate();
    }
    ret = NodeManager::currentNM()->mkNode(OR, nret, n_str_ind);
  }
  Trace("quantifiers-sk-debug") << "mkSkolem body for " << f
                                << " returns : " << ret << std::endl;
  // if it has an instantiation level, set the skolemized body to that level
  if (f.hasAttribute(InstLevelAttribute()))
  {
    QuantAttributes::setInstantiationLevelAttr(
        ret, f.getAttribute(InstLevelAttribute()));
  }

  if (Trace.isOn("quantifiers-sk"))
  {
    Trace("quantifiers-sk") << "Skolemize : ";
    for (unsigned i = 0; i < sk.size(); i++)
    {
      Trace("quantifiers-sk") << sk[i] << " ";
    }
    Trace("quantifiers-sk") << "for " << std::endl;
    Trace("quantifiers-sk") << "   " << f << std::endl;
  }

  return ret;
}

Node Skolemize::getSkolemizedBody(Node f)
{
  Assert(f.getKind() == FORALL);
  if (d_skolem_body.find(f) == d_skolem_body.end())
  {
    std::vector<TypeNode> fvTypes;
    std::vector<TNode> fvs;
    Node sub;
    std::vector<unsigned> sub_vars;
    d_skolem_body[f] = mkSkolemizedBody(
        f, f[1], fvTypes, fvs, d_skolem_constants[f], sub, sub_vars);
    // store sub quantifier information
    if (!sub.isNull())
    {
      // if we are skolemizing one at a time, we already know the skolem
      // constants of the sub-quantified formula, store them
      Assert(d_skolem_constants[sub].empty());
      for (unsigned i = 0; i < sub_vars.size(); i++)
      {
        d_skolem_constants[sub].push_back(d_skolem_constants[f][sub_vars[i]]);
      }
    }
    Assert(d_skolem_constants[f].size() == f[0].getNumChildren());
    if (options::sortInference())
    {
      for (unsigned i = 0; i < d_skolem_constants[f].size(); i++)
      {
        // carry information for sort inference
        d_quantEngine->getTheoryEngine()->getSortInference()->setSkolemVar(
            f, f[0][i], d_skolem_constants[f][i]);
      }
    }
  }
  return d_skolem_body[f];
}

bool Skolemize::isInductionTerm(Node n)
{
  TypeNode tn = n.getType();
  if (options::dtStcInduction() && tn.isDatatype())
  {
    const DType& dt = tn.getDType();
    return !dt.isCodatatype();
  }
  if (options::intWfInduction() && n.getType().isInteger())
  {
    return true;
  }
  return false;
}

bool Skolemize::printSkolemization(std::ostream& out)
{
  bool printed = false;
  for (NodeNodeMap::iterator it = d_skolemized.begin();
       it != d_skolemized.end();
       ++it)
  {
    Node q = (*it).first;
    printed = true;
    out << "(skolem " << q << std::endl;
    out << "  ( ";
    for (unsigned i = 0; i < d_skolem_constants[q].size(); i++)
    {
      if (i > 0)
      {
        out << " ";
      }
      out << d_skolem_constants[q][i];
    }
    out << " )" << std::endl;
    out << ")" << std::endl;
  }
  return printed;
}

} /* CVC4::theory::quantifiers namespace */
} /* CVC4::theory namespace */
} /* CVC4 namespace */
