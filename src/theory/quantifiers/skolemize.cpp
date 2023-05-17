/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Mathias Preiner, Andres Noetzli
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Implementation of skolemization utility.
 */

#include "theory/quantifiers/skolemize.h"

#include "expr/dtype.h"
#include "expr/dtype_cons.h"
#include "expr/skolem_manager.h"
#include "options/quantifiers_options.h"
#include "options/smt_options.h"
#include "proof/proof.h"
#include "proof/proof_node_manager.h"
#include "theory/quantifiers/quantifiers_attributes.h"
#include "theory/quantifiers/quantifiers_state.h"
#include "theory/quantifiers/term_registry.h"
#include "theory/quantifiers/term_util.h"
#include "theory/rewriter.h"
#include "theory/sort_inference.h"
#include "util/rational.h"

using namespace cvc5::internal::kind;

namespace cvc5::internal {
namespace theory {
namespace quantifiers {

Skolemize::Skolemize(Env& env, QuantifiersState& qs, TermRegistry& tr)
    : EnvObj(env),
      d_qstate(qs),
      d_treg(tr),
      d_skolemized(userContext()),
      d_epg(!isProofEnabled()
                ? nullptr
                : new EagerProofGenerator(env, userContext(), "Skolemize::epg"))
{
}

TrustNode Skolemize::process(Node q)
{
  Assert(q.getKind() == FORALL);
  // do skolemization
  if (d_skolemized.find(q) != d_skolemized.end())
  {
    return TrustNode::null();
  }
  Node lem;
  ProofGenerator* pg = nullptr;
  if (isProofEnabled() && !options().quantifiers.dtStcInduction
      && !options().quantifiers.intWfInduction)
  {
    ProofNodeManager * pnm = d_env.getProofNodeManager();
    // if using proofs and not using induction, we use the justified
    // skolemization
    NodeManager* nm = NodeManager::currentNM();
    std::vector<Node> echildren(q.begin(), q.end());
    echildren[1] = echildren[1].notNode();
    Node existsq = nm->mkNode(EXISTS, echildren);
    std::vector<Node> vars(existsq[0].begin(), existsq[0].end());
    // cache the skolems in d_skolem_constants[q]
    std::vector<Node>& skolems = d_skolem_constants[q];
    skolems = getSkolemConstants(existsq);
    Node res = existsq[1].substitute(
        vars.begin(), vars.end(), skolems.begin(), skolems.end());
    Node qnot = q.notNode();
    CDProof cdp(d_env);
    cdp.addStep(res, PfRule::SKOLEMIZE, {qnot}, {});
    std::shared_ptr<ProofNode> pf = cdp.getProofFor(res);
    std::vector<Node> assumps;
    assumps.push_back(qnot);
    std::shared_ptr<ProofNode> pfs = pnm->mkScope({pf}, assumps);
    lem = nm->mkNode(IMPLIES, qnot, res);
    d_epg->setProofFor(lem, pfs);
    pg = d_epg.get();
    Trace("quantifiers-sk")
        << "Skolemize (with proofs) : " << d_skolem_constants[q] << " for "
        << std::endl;
    Trace("quantifiers-sk") << "   " << q << std::endl;
    Trace("quantifiers-sk") << "   " << res << std::endl;
  }
  else
  {
    // otherwise, we use the more general skolemization with inductive
    // strengthening, which does not support proofs
    Node body = getSkolemizedBodyInduction(q);
    NodeBuilder nb(kind::OR);
    nb << q << body.notNode();
    lem = nb;
  }
  d_skolemized[q] = lem;
  // triggered when skolemizing
  d_treg.processSkolemization(q, d_skolem_constants[q]);
  return TrustNode::mkTrustLemma(lem, pg);
}

std::vector<Node> Skolemize::getSkolemConstants(const Node& q)
{
  Assert(q.getKind() == EXISTS);
  std::vector<Node> skolems;
  for (size_t i = 0, nvars = q[0].getNumChildren(); i < nvars; i++)
  {
    skolems.push_back(getSkolemConstant(q, i));
  }
  return skolems;
}

Node Skolemize::getSkolemConstant(const Node& q, size_t i)
{
  Assert(q.getKind() == EXISTS);
  Assert(i < q[0].getNumChildren());
  NodeManager* nm = NodeManager::currentNM();
  SkolemManager* sm = nm->getSkolemManager();
  Node r = nm->mkConstInt(Rational(i));
  std::vector<Node> cacheVals{q, r};
  return sm->mkSkolemFunction(
      SkolemFunId::QUANTIFIERS_SKOLEMIZE, q[0][i].getType(), cacheVals);
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
    tspec = dc.getInstantiatedConstructorType(n.getType());
    Trace("sk-ind-debug") << "Instantiated constructor type : " << tspec
                          << std::endl;
    Assert(tspec.getNumChildren() == dc.getNumArgs());
  }
  Trace("sk-ind-debug") << "Check self sel " << dc.getName() << " "
                        << dt.getName() << std::endl;
  NodeManager* nm = NodeManager::currentNM();
  for (unsigned j = 0; j < dc.getNumArgs(); j++)
  {
    if (dt.isParametric())
    {
      Trace("sk-ind-debug") << "Compare " << tspec[j] << " " << ntn
                            << std::endl;
      if (tspec[j] != ntn)
      {
        continue;
      }
    }
    else
    {
      TypeNode tn = dc[j].getRangeType();
      Trace("sk-ind-debug") << "Compare " << tn << " " << ntn << std::endl;
      if (tn != ntn)
      {
        continue;
      }
    }
    // do not use shared selectors
    Node ss = nm->mkNode(APPLY_SELECTOR, dc.getSelector(j), n);
    if (std::find(selfSel.begin(), selfSel.end(), ss) == selfSel.end())
    {
      selfSel.push_back(ss);
    }
  }
}

bool Skolemize::getSkolemConstantsInduction(Node q, std::vector<Node>& skolems)
{
  std::unordered_map<Node, std::vector<Node>>::iterator it =
      d_skolem_constants.find(q);
  if (it != d_skolem_constants.end())
  {
    skolems.insert(skolems.end(), it->second.begin(), it->second.end());
    return true;
  }
  return false;
}

Node Skolemize::mkSkolemizedBodyInduction(const Options& opts,
                                          Node f,
                                          Node n,
                                          std::vector<TNode>& fvs,
                                          std::vector<Node>& sk,
                                          Node& sub,
                                          std::vector<unsigned>& sub_vars)
{
  NodeManager* nm = NodeManager::currentNM();
  // compute the argument types from the free variables
  std::vector<TypeNode> argTypes;
  for (TNode v : fvs)
  {
    argTypes.push_back(v.getType());
  }
  SkolemManager* sm = nm->getSkolemManager();
  Assert(sk.empty() || sk.size() == f[0].getNumChildren());
  // calculate the variables and substitution
  std::vector<TNode> ind_vars;
  std::vector<unsigned> ind_var_indicies;
  std::vector<TNode> vars;
  std::vector<unsigned> var_indicies;
  for (unsigned i = 0; i < f[0].getNumChildren(); i++)
  {
    if (isInductionTerm(opts, f[0][i]))
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
        s = sm->mkDummySkolem(
            "skv", f[0][i].getType(), "created during skolemization");
      }
      else
      {
        TypeNode typ = nm->mkFunctionType(argTypes, f[0][i].getType());
        Node op = sm->mkDummySkolem(
            "skop", typ, "op created during pre-skolemization");
        // DOTHIS: set attribute on op, marking that it should not be selected
        // as trigger
        std::vector<Node> funcArgs;
        funcArgs.push_back(op);
        funcArgs.insert(funcArgs.end(), fvs.begin(), fvs.end());
        s = nm->mkNode(kind::APPLY_UF, funcArgs);
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
    if (opts.quantifiers.dtStcInduction && tn.isDatatype())
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
        disj.push_back(conj.size() == 1 ? conj[0] : nm->mkNode(OR, conj));
      }
      Assert(!disj.empty());
      n_str_ind = disj.size() == 1 ? disj[0] : nm->mkNode(AND, disj);
    }
    else if (opts.quantifiers.intWfInduction && tn.isInteger())
    {
      Node icond = nm->mkNode(GEQ, k, nm->mkConstInt(Rational(0)));
      Node iret =
          ret.substitute(ind_vars[0],
                         nm->mkNode(SUB, k, nm->mkConstInt(Rational(1))))
              .negate();
      n_str_ind = nm->mkNode(OR, icond.negate(), iret);
      n_str_ind = nm->mkNode(AND, icond, n_str_ind);
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
      Node bvl = nm->mkNode(BOUND_VAR_LIST, rem_ind_vars);
      nret = nm->mkNode(FORALL, bvl, nret);
      sub = nret;
      sub_vars.insert(
          sub_vars.end(), ind_var_indicies.begin() + 1, ind_var_indicies.end());
      n_str_ind = nm->mkNode(FORALL, bvl, n_str_ind.negate()).negate();
    }
    ret = nm->mkNode(OR, nret, n_str_ind);
  }
  Trace("quantifiers-sk-debug") << "mkSkolem body for " << f
                                << " returns : " << ret << std::endl;
  // if it has an instantiation level, set the skolemized body to that level
  if (f.hasAttribute(InstLevelAttribute()))
  {
    QuantAttributes::setInstantiationLevelAttr(
        ret, f.getAttribute(InstLevelAttribute()));
  }

  Trace("quantifiers-sk") << "Skolemize : " << sk << " for " << std::endl;
  Trace("quantifiers-sk") << "   " << f << std::endl;

  return ret;
}

Node Skolemize::getSkolemizedBodyInduction(Node f)
{
  Assert(f.getKind() == FORALL);
  std::unordered_map<Node, Node>::iterator it = d_skolem_body.find(f);
  if (it == d_skolem_body.end())
  {
    std::vector<TNode> fvs;
    Node sub;
    std::vector<unsigned> sub_vars;
    Node ret = mkSkolemizedBodyInduction(
        options(), f, f[1], fvs, d_skolem_constants[f], sub, sub_vars);
    d_skolem_body[f] = ret;
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
    SortInference* si = d_qstate.getSortInference();
    if (si != nullptr)
    {
      for (unsigned i = 0; i < d_skolem_constants[f].size(); i++)
      {
        // carry information for sort inference
        si->setSkolemVar(f, f[0][i], d_skolem_constants[f][i]);
      }
    }
    return ret;
  }
  return it->second;
}

bool Skolemize::isInductionTerm(const Options& opts, Node n)
{
  TypeNode tn = n.getType();
  if (opts.quantifiers.dtStcInduction && tn.isDatatype())
  {
    const DType& dt = tn.getDType();
    return !dt.isCodatatype();
  }
  if (opts.quantifiers.intWfInduction && tn.isInteger())
  {
    return true;
  }
  return false;
}

void Skolemize::getSkolemTermVectors(
    std::map<Node, std::vector<Node> >& sks) const
{
  std::unordered_map<Node, std::vector<Node>>::const_iterator itk;
  for (const auto& p : d_skolemized)
  {
    Node q = p.first;
    itk = d_skolem_constants.find(q);
    Assert(itk != d_skolem_constants.end());
    sks[q].insert(sks[q].end(), itk->second.begin(), itk->second.end());
  }
}

bool Skolemize::isProofEnabled() const
{
  return d_env.isTheoryProofProducing();
}

}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal
