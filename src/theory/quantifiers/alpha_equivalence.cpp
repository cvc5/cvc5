/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Aina Niemetz, Hans-Joerg Schurr
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2025 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Alpha equivalence checking.
 */

#include "theory/quantifiers/alpha_equivalence.h"

#include "expr/node_algorithm.h"
#include "proof/method_id.h"
#include "proof/proof.h"
#include "proof/proof_node.h"
#include "theory/builtin/proof_checker.h"

using namespace cvc5::internal::kind;

namespace cvc5::internal {
namespace theory {
namespace quantifiers {

struct sortTypeOrder {
  expr::TermCanonize* d_tu;
  bool operator() (TypeNode i, TypeNode j) {
    return d_tu->getIdForType( i )<d_tu->getIdForType( j );
  }
};

AlphaEquivalenceTypeNode::AlphaEquivalenceTypeNode(context::Context* c)
    : d_quant(c)
{
}

Node AlphaEquivalenceTypeNode::registerNode(
    context::Context* c,
    Node q,
    Node t,
    std::vector<TypeNode>& typs,
    std::map<TypeNode, size_t>& typCount)
{
  AlphaEquivalenceTypeNode* aetn = this;
  size_t index = 0;
  std::map<std::pair<TypeNode, size_t>,
           std::unique_ptr<AlphaEquivalenceTypeNode>>::iterator itc;
  while (index < typs.size())
  {
    TypeNode curr = typs[index];
    Assert(typCount.find(curr) != typCount.end());
    Trace("aeq-debug") << "[" << curr << " " << typCount[curr] << "] ";
    std::pair<TypeNode, size_t> key(curr, typCount[curr]);
    itc = aetn->d_children.find(key);
    if (itc == aetn->d_children.end())
    {
      aetn->d_children[key] = std::make_unique<AlphaEquivalenceTypeNode>(c);
      aetn = aetn->d_children[key].get();
    }
    else
    {
      aetn = itc->second.get();
    }
    index = index + 1;
  }
  Trace("aeq-debug") << " : ";
  NodeMap::iterator it = aetn->d_quant.find(t);
  if (it != aetn->d_quant.end() && !it->second.isNull())
  {
    Trace("aeq-debug") << it->second << std::endl;
    return it->second;
  }
  Trace("aeq-debug") << "(new)" << std::endl;
  aetn->d_quant[t] = q;
  return q;
}

AlphaEquivalenceDb::AlphaEquivalenceDb(context::Context* c,
                                       expr::TermCanonize* tc,
                                       bool sortCommChildren)
    : d_context(c),
      d_ae_typ_trie(c),
      d_tc(tc),
      d_sortCommutativeOpChildren(sortCommChildren)
{
}
Node AlphaEquivalenceDb::addTerm(Node q)
{
  Assert(q.getKind() == Kind::FORALL);
  Trace("aeq") << "Alpha equivalence : register " << q << std::endl;
  //construct canonical quantified formula
  Node t = d_tc->getCanonicalTerm(q[1], d_sortCommutativeOpChildren);
  Trace("aeq") << "  canonical form: " << t << std::endl;
  return addTermToTypeTrie(t, q);
}

Node AlphaEquivalenceDb::addTermWithSubstitution(Node q,
                                                 std::vector<Node>& vars,
                                                 std::vector<Node>& subs)
{
  Trace("aeq") << "Alpha equivalence : register " << q << std::endl;
  // construct canonical quantified formula with visited cache
  std::map<TNode, Node> visited;
  Node t = d_tc->getCanonicalTerm(q[1], visited, d_sortCommutativeOpChildren);
  // only need to store BOUND_VARIABLE in substitution
  std::map<Node, TNode>& bm = d_bvmap[q];
  for (const std::pair<const TNode, Node>& b : visited)
  {
    if (b.first.getKind() == Kind::BOUND_VARIABLE)
    {
      Assert(b.second.getKind() == Kind::BOUND_VARIABLE);
      bm[b.second] = b.first;
    }
  }
  Node qret = addTermToTypeTrie(t, q);
  if (qret != q)
  {
    Assert(d_bvmap.find(qret) != d_bvmap.end());
    std::map<Node, TNode>& bmr = d_bvmap[qret];
    std::map<Node, TNode>::iterator itb;
    for (const std::pair<const Node, TNode>& b : bmr)
    {
      itb = bm.find(b.first);
      if (itb == bm.end())
      {
        // didn't use the same variables, fail
        vars.clear();
        subs.clear();
        break;
      }
      // otherwise, we map the variable in the returned quantified formula
      // to the variable that used the same canonical variable
      vars.push_back(b.second);
      subs.push_back(itb->second);
    }
  }
  return qret;
}

Node AlphaEquivalenceDb::addTermToTypeTrie(Node t, Node q)
{
  //compute variable type counts
  std::map<TypeNode, size_t> typCount;
  std::vector< TypeNode > typs;
  for (const Node& v : q[0])
  {
    TypeNode tn = v.getType();
    typCount[tn]++;
    if( std::find( typs.begin(), typs.end(), tn )==typs.end() ){
      typs.push_back( tn );
    }
  }
  sortTypeOrder sto;
  sto.d_tu = d_tc;
  std::sort( typs.begin(), typs.end(), sto );
  Trace("aeq-debug") << "  ";
  Node ret = d_ae_typ_trie.registerNode(d_context, q, t, typs, typCount);
  Trace("aeq") << "  ...result : " << ret << std::endl;
  return ret;
}

AlphaEquivalence::AlphaEquivalence(Env& env)
    : EnvObj(env),
      d_termCanon(),
      d_aedb(userContext(), &d_termCanon, true),
      d_pfAlpha(env.isTheoryProofProducing() ? new EagerProofGenerator(env)
                                             : nullptr)
{
}

TrustNode AlphaEquivalence::reduceQuantifier(Node q)
{
  Assert(q.getKind() == Kind::FORALL);
  Node ret;
  std::vector<Node> vars;
  std::vector<Node> subs;
  if (isProofEnabled())
  {
    ret = d_aedb.addTermWithSubstitution(q, vars, subs);
  }
  else
  {
    ret = d_aedb.addTerm(q);
  }
  if (ret == q)
  {
    return TrustNode::null();
  }
  Node lem;
  ProofGenerator* pg = nullptr;
  // lemma ( q <=> d_quant )
  // Notice that we infer this equivalence regardless of whether q or ret
  // have annotations (e.g. user patterns, names, etc.).
  Trace("alpha-eq") << "Alpha equivalent : " << std::endl;
  Trace("alpha-eq") << "  " << q << std::endl;
  Trace("alpha-eq") << "  " << ret << std::endl;
  lem = ret.eqNode(q);
  if (q.getNumChildren() == 3)
  {
    verbose(1) << "Ignoring annotated quantified formula based on alpha "
                  "equivalence: "
               << q << std::endl;
  }
  // if successfully computed the substitution above
  if (isProofEnabled() && !vars.empty())
  {
    NodeManager* nm = nodeManager();
    Node proveLem = lem;
    CDProof cdp(d_env);
    // remove patterns from both sides
    if (q.getNumChildren() == 3)
    {
      Node qo = q;
      q = builtin::BuiltinProofRuleChecker::getEncodeEqIntro(nm, q);
      if (q != qo)
      {
        Node eqq = qo.eqNode(q);
        cdp.addStep(eqq, ProofRule::ENCODE_EQ_INTRO, {}, {qo});
        Node eqqs = q.eqNode(qo);
        cdp.addStep(eqqs, ProofRule::SYMM, {eqq}, {});
        Node eqq2 = ret.eqNode(q);
        cdp.addStep(proveLem, ProofRule::TRANS, {eqq2, eqqs}, {});
        proveLem = eqq2;
      }
    }
    if (ret.getNumChildren() == 3)
    {
      Node reto = ret;
      ret = builtin::BuiltinProofRuleChecker::getEncodeEqIntro(nm, ret);
      if (ret != reto)
      {
        Node eqq = reto.eqNode(ret);
        cdp.addStep(eqq, ProofRule::ENCODE_EQ_INTRO, {}, {reto});
        Node eqq2 = ret.eqNode(q);
        cdp.addStep(proveLem, ProofRule::TRANS, {eqq, eqq2}, {});
        proveLem = eqq2;
      }
    }
    if (Configuration::isAssertionBuild())
    {
      // all variables should be unique since we are processing rewritten
      // quantified formulas
      std::unordered_set<Node> vset(vars.begin(), vars.end());
      Assert(vset.size() == vars.size());
      std::unordered_set<Node> sset(subs.begin(), subs.end());
      Assert(sset.size() == subs.size());
    }
    std::vector<Node> transEq;
    // if there is variable shadowing, we do an intermediate step with fresh
    // variables
    if (expr::hasSubterm(ret, subs))
    {
      std::vector<Node> isubs;
      for (const Node& v : subs)
      {
        isubs.emplace_back(NodeManager::mkBoundVar(v.getType()));
      }
      // ---------- ALPHA_EQUIV
      // ret = iret
      Node ieq = addAlphaEquivStep(cdp, ret, vars, isubs);
      transEq.emplace_back(ieq);
      ret = ieq[1];
      vars = isubs;
    }
    // ---------- ALPHA_EQUIV
    // ret = sret
    Node eq = addAlphaEquivStep(cdp, ret, vars, subs);
    Assert(eq.getKind() == Kind::EQUAL);
    Node sret = eq[1];
    transEq.emplace_back(eq);
    Assert(sret.getKind() == Kind::FORALL);
    if (sret[0] != q[0])
    {
      // variable reorder?
      std::vector<Node> children;
      children.push_back(q[0]);
      children.push_back(sret[1]);
      if (sret.getNumChildren() == 3)
      {
        children.push_back(sret[2]);
      }
      Node sreorder = nm->mkNode(Kind::FORALL, children);
      Node eqqr = sret.eqNode(sreorder);
      if (cdp.addStep(eqqr, ProofRule::QUANT_VAR_REORDERING, {}, {eqqr}))
      {
        transEq.push_back(eqqr);
        sret = sreorder;
      }
      // if var reordering did not apply, we likely will not succeed below
    }
    // if not syntactically equal, maybe it can be transformed
    bool success = false;
    if (sret == q)
    {
      success = true;
    }
    else
    {
      Node eq2 = sret.eqNode(q);
      transEq.push_back(eq2);
      Node eq2r = extendedRewrite(eq2);
      if (eq2r.isConst() && eq2r.getConst<bool>())
      {
        // ---------- MACRO_SR_PRED_INTRO
        // sret = q
        std::vector<Node> pfArgs2;
        pfArgs2.push_back(eq2);
        addMethodIds(nodeManager(),
                     pfArgs2,
                     MethodId::SB_DEFAULT,
                     MethodId::SBA_SEQUENTIAL,
                     MethodId::RW_EXT_REWRITE);
        cdp.addStep(eq2, ProofRule::MACRO_SR_PRED_INTRO, {}, pfArgs2);
        success = true;
      }
    }
    // if successful, store the proof and remember the proof generator
    if (success)
    {
      if (transEq.size() > 1)
      {
        // TRANS of ALPHA_EQ and MACRO_SR_PRED_INTRO steps from above
        cdp.addStep(proveLem, ProofRule::TRANS, transEq, {});
      }
      std::shared_ptr<ProofNode> pn = cdp.getProofFor(lem);
      Trace("alpha-eq") << "Proof is " << *pn.get() << std::endl;
      d_pfAlpha->setProofFor(lem, pn);
      pg = d_pfAlpha.get();
    }
  }
  return TrustNode::mkTrustLemma(lem, pg);
}

Node AlphaEquivalence::addAlphaEquivStep(CDProof& cdp,
                                         const Node& f,
                                         const std::vector<Node>& vars,
                                         const std::vector<Node>& subs)
{
  std::vector<Node> pfArgs;
  pfArgs.push_back(f);
  NodeManager* nm = nodeManager();
  pfArgs.push_back(nm->mkNode(Kind::SEXPR, vars));
  pfArgs.push_back(nm->mkNode(Kind::SEXPR, subs));
  Node sf = f.substitute(vars.begin(), vars.end(), subs.begin(), subs.end());
  std::vector<Node> transEq;
  Node eq = f.eqNode(sf);
  cdp.addStep(eq, ProofRule::ALPHA_EQUIV, {}, pfArgs);
  // if not syntactically equal, maybe it can be transform
  return eq;
}

bool AlphaEquivalence::isProofEnabled() const { return d_pfAlpha != nullptr; }

}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal
