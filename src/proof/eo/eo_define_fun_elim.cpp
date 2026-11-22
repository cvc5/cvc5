/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Eliminates higher-order define-fun equalities from CPC proofs.
 */

#include "proof/eo/eo_define_fun_elim.h"

#include <algorithm>

#include "expr/node_algorithm.h"
#include "expr/node_builder.h"
#include "proof/proof_node_algorithm.h"
#include "proof/proof_node_manager.h"
#include "rewriter/rewrites.h"

namespace cvc5::internal {
namespace proof {

EoDefineFunElim::EoDefineFunElim(Env& env) : EnvObj(env), d_failed(false) {}

bool EoDefineFunElim::isDefEq(const Node& n) const
{
  return n.getKind() == Kind::EQUAL && n[1].getKind() == Kind::LAMBDA
         && d_defSyms.find(n[0]) != d_defSyms.end();
}

std::shared_ptr<ProofNode> EoDefineFunElim::mk(
    ProofRule r,
    const std::vector<std::shared_ptr<ProofNode>>& children,
    const std::vector<Node>& args,
    const Node& expected)
{
  std::shared_ptr<ProofNode> pn =
      d_env.getProofNodeManager()->mkNode(r, children, args, expected);
  if (pn == nullptr)
  {
    Trace("eo-dfe") << "...failed to make " << r << " for " << expected
                    << std::endl;
    d_failed = true;
  }
  return pn;
}

Node EoDefineFunElim::convert(const Node& n)
{
  std::unordered_map<Node, Node>::iterator it = d_cache.find(n);
  if (it != d_cache.end())
  {
    return it->second;
  }
  NodeManager* nm = nodeManager();
  Node ret;
  Kind k = n.getKind();
  if (k == Kind::APPLY_UF && n.getOperator().getKind() == Kind::LAMBDA)
  {
    // beta-reduce
    Node lam = n.getOperator();
    Node body = convert(lam[1]);
    std::vector<Node> vars(lam[0].begin(), lam[0].end());
    std::vector<Node> subs;
    for (const Node& nc : n)
    {
      subs.push_back(convert(nc));
    }
    if (vars.size() == subs.size())
    {
      ret = body.substitute(vars.begin(), vars.end(), subs.begin(), subs.end());
    }
    else
    {
      d_failed = true;
      ret = n;
    }
  }
  else if (k == Kind::HO_APPLY)
  {
    // collect the arguments of a curried application
    std::vector<Node> hargs;
    Node h = n;
    while (h.getKind() == Kind::HO_APPLY)
    {
      hargs.push_back(h[1]);
      h = h[0];
    }
    if (h.getKind() == Kind::LAMBDA && hargs.size() == h[0].getNumChildren())
    {
      // fully applied lambda, beta-reduce
      std::reverse(hargs.begin(), hargs.end());
      Node body = convert(h[1]);
      std::vector<Node> vars(h[0].begin(), h[0].end());
      std::vector<Node> subs;
      for (const Node& a : hargs)
      {
        subs.push_back(convert(a));
      }
      ret = body.substitute(vars.begin(), vars.end(), subs.begin(), subs.end());
    }
    else
    {
      ret = nodeManager()->mkNode(Kind::HO_APPLY, convert(n[0]), convert(n[1]));
    }
  }
  else if (isDefEq(n))
  {
    // (= f (lambda x t)) becomes (forall x (= (f x) t))
    Node lam = n[1];
    std::vector<Node> app{n[0]};
    app.insert(app.end(), lam[0].begin(), lam[0].end());
    Node fx = nm->mkNode(Kind::APPLY_UF, app);
    ret = nm->mkNode(Kind::FORALL, lam[0], fx.eqNode(convert(lam[1])));
  }
  else if (n.getNumChildren() == 0)
  {
    ret = n;
  }
  else
  {
    if (k == Kind::LAMBDA)
    {
      // a lambda that is not handled above, we fail
      Trace("eo-dfe") << "...remaining lambda " << n << std::endl;
      d_failed = true;
    }
    NodeBuilder nb(nm, k);
    if (n.getMetaKind() == kind::metakind::PARAMETERIZED)
    {
      nb << convert(n.getOperator());
    }
    for (const Node& nc : n)
    {
      nb << convert(nc);
    }
    ret = nb.constructNode();
  }
  d_cache[n] = ret;
  return ret;
}

std::shared_ptr<ProofNode> EoDefineFunElim::proveCongSubst(
    const Node& t,
    const std::vector<Node>& vars,
    const std::vector<Node>& as,
    const std::vector<Node>& bs,
    const std::vector<std::shared_ptr<ProofNode>>& pfs,
    std::unordered_map<Node, std::shared_ptr<ProofNode>>& cache)
{
  auto it = cache.find(t);
  if (it != cache.end())
  {
    return it->second;
  }
  std::shared_ptr<ProofNode> ret;
  Node ta = t.substitute(vars.begin(), vars.end(), as.begin(), as.end());
  Node tb = t.substitute(vars.begin(), vars.end(), bs.begin(), bs.end());
  std::vector<Node>::const_iterator itv =
      std::find(vars.begin(), vars.end(), t);
  if (itv != vars.end())
  {
    ret = pfs[itv - vars.begin()];
  }
  else if (ta == tb)
  {
    ret = mk(ProofRule::REFL, {}, {ta}, ta.eqNode(tb));
  }
  else if (t.getNumChildren() == 0)
  {
    Trace("eo-dfe") << "...cannot prove congruence for " << t << std::endl;
    d_failed = true;
  }
  else
  {
    if (t.isClosure())
    {
      // We require the bound variables of t to be distinct from the
      // substitution domain and not to occur free in its range, so that
      // congruence over the binder is sound.
      for (const Node& v : t[0])
      {
        if (std::find(vars.begin(), vars.end(), v) != vars.end()
            || std::any_of(as.begin(),
                           as.end(),
                           [&v](const Node& a) { return expr::hasSubterm(a, v); })
            || std::any_of(bs.begin(),
                           bs.end(),
                           [&v](const Node& b) { return expr::hasSubterm(b, v); }))
        {
          Trace("eo-dfe") << "...cannot prove congruence under binder " << t
                          << std::endl;
          d_failed = true;
          return nullptr;
        }
      }
    }
    std::vector<std::shared_ptr<ProofNode>> cps;
    // for closures, we skip the bound variable list
    for (size_t i = t.isClosure() ? 1 : 0, nchild = t.getNumChildren();
         i < nchild;
         i++)
    {
      const Node& tc = t[i];
      cps.push_back(proveCongSubst(tc, vars, as, bs, pfs, cache));
      if (d_failed)
      {
        return nullptr;
      }
    }
    std::vector<Node> cargs;
    ProofRule cr = expr::getCongRule(ta, cargs);
    ret = mk(cr, cps, cargs, ta.eqNode(tb));
  }
  cache[t] = ret;
  return ret;
}

std::shared_ptr<ProofNode> EoDefineFunElim::convertDefProof(
    std::shared_ptr<ProofNode> pn)
{
  auto it = d_pcache.find(pn.get());
  if (it != d_pcache.end())
  {
    return it->second;
  }
  NodeManager* nm = nodeManager();
  Node res = pn->getResult();
  Assert(isDefEq(res));
  ProofRule r = pn->getRule();
  std::shared_ptr<ProofNode> ret;
  if (r == ProofRule::ASSUME)
  {
    Node nres = convert(res);
    ret = mk(ProofRule::ASSUME, {}, {nres}, nres);
  }
  else if (r == ProofRule::TRANS
           && isDefEq(pn->getChildren()[0]->getResult()))
  {
    const std::vector<std::shared_ptr<ProofNode>>& cs = pn->getChildren();
    std::shared_ptr<ProofNode> cur = convertDefProof(cs[0]);
    for (size_t i = 1, nchild = cs.size(); i < nchild && !d_failed; i++)
    {
      if (cs[i]->getRule() == ProofRule::REFL)
      {
        continue;
      }
      if (cs[i]->getRule() != ProofRule::CONG
          || cs[i]->getChildren().size() != 1)
      {
        Trace("eo-dfe") << "...unhandled lambda equality proof "
                        << cs[i]->getRule() << std::endl;
        d_failed = true;
        break;
      }
      // the body equality (= s1 s2), with lambdas beta-reduced
      std::shared_ptr<ProofNode> pbody = convertProof(cs[i]->getChildren()[0]);
      if (d_failed)
      {
        break;
      }
      Node q = cur->getResult();
      Node beq = pbody->getResult();
      Assert(q.getKind() == Kind::FORALL);
      if (beq.getKind() != Kind::EQUAL || beq[0] != q[1][1])
      {
        Trace("eo-dfe") << "...body mismatch " << beq << " / " << q
                        << std::endl;
        d_failed = true;
        break;
      }
      Node fx = q[1][0];
      Node newEq = fx.eqNode(beq[1]);
      Node q2 = nm->mkNode(Kind::FORALL, q[0], newEq);
      //  ------- REFL   ----------- (converted)
      //  fx = fx        s1 = s2
      //  -------------------------- CONG
      //  (= fx s1) = (= fx s2)
      //  -------------------------- CONG
      //  (forall x (= fx s1)) = (forall x (= fx s2))
      std::shared_ptr<ProofNode> prefl =
          mk(ProofRule::REFL, {}, {fx}, fx.eqNode(fx));
      std::vector<Node> cargs;
      ProofRule cr = expr::getCongRule(q[1], cargs);
      std::shared_ptr<ProofNode> pc1 =
          mk(cr, {prefl, pbody}, cargs, q[1].eqNode(newEq));
      if (d_failed)
      {
        break;
      }
      cargs.clear();
      cr = expr::getCongRule(q, cargs);
      std::shared_ptr<ProofNode> pc2 = mk(cr, {pc1}, cargs, q.eqNode(q2));
      if (d_failed)
      {
        break;
      }
      cur = mk(ProofRule::EQ_RESOLVE, {cur, pc2}, {}, q2);
    }
    ret = cur;
  }
  else
  {
    Trace("eo-dfe") << "...unhandled definition proof " << r << " for " << res
                    << std::endl;
    d_failed = true;
  }
  if (ret == nullptr)
  {
    d_failed = true;
    ret = pn;
  }
  d_pcache[pn.get()] = ret;
  return ret;
}

std::shared_ptr<ProofNode> EoDefineFunElim::convertProof(
    std::shared_ptr<ProofNode> pn)
{
  auto it = d_pcache.find(pn.get());
  if (it != d_pcache.end())
  {
    return it->second;
  }
  if (d_failed)
  {
    return pn;
  }
  NodeManager* nm = nodeManager();
  Node res = pn->getResult();
  ProofRule r = pn->getRule();
  const std::vector<std::shared_ptr<ProofNode>>& cs = pn->getChildren();
  const std::vector<Node>& args = pn->getArguments();
  std::shared_ptr<ProofNode> ret;
  ProofRewriteRule prid;
  if (isDefEq(res))
  {
    ret = convertDefProof(pn);
  }
  else if (r == ProofRule::HO_CONG && !cs.empty()
           && isDefEq(cs[0]->getResult()) && res[0].getKind() == Kind::APPLY_UF
           && res[0].getNumChildren() + 1 == cs.size())
  {
    // (f a) = ((lambda x t) b) becomes
    //
    //                     --------------------- (converted)
    //  ------------ CONG  forall x (= (f x) t)
    //  (f a) = (f b)      --------------------- INSTANTIATE
    //                     (f b) = t[b/x]
    //  ---------------------------------------- TRANS
    //  (f a) = t[b/x]
    std::shared_ptr<ProofNode> p0 = convertDefProof(cs[0]);
    Node q = p0->getResult();
    std::vector<Node> as, bs;
    std::vector<std::shared_ptr<ProofNode>> eqs;
    for (size_t i = 1, nchild = cs.size(); i < nchild; i++)
    {
      Node eq = cs[i]->getResult();
      as.push_back(convert(eq[0]));
      bs.push_back(convert(eq[1]));
      eqs.push_back(convertProof(cs[i]));
    }
    if (d_failed || q.getKind() != Kind::FORALL
        || q[0].getNumChildren() != bs.size())
    {
      d_failed = true;
      return pn;
    }
    std::vector<Node> vars(q[0].begin(), q[0].end());
    Node inst = q[1].substitute(vars.begin(), vars.end(), bs.begin(), bs.end());
    Node sx = nm->mkNode(Kind::SEXPR, bs);
    ret = mk(ProofRule::INSTANTIATE, {p0}, {sx}, inst);
    if (as != bs && !d_failed)
    {
      Node fa = res[0];
      Assert(fa == convert(fa));
      Node fb = inst[0];
      std::vector<Node> cargs;
      ProofRule cr = expr::getCongRule(fa, cargs);
      std::shared_ptr<ProofNode> pc = mk(cr, eqs, cargs, fa.eqNode(fb));
      if (!d_failed)
      {
        ret = mk(ProofRule::TRANS, {pc, ret}, {}, fa.eqNode(inst[1]));
      }
    }
  }
  else if (r == ProofRule::CONG && res[0].getKind() == Kind::APPLY_UF
           && res[0].getOperator().getKind() == Kind::LAMBDA
           && res[1].getKind() == Kind::APPLY_UF
           && res[1].getOperator() == res[0].getOperator()
           && cs.size() == res[0].getNumChildren())
  {
    // ((lambda x t) a) = ((lambda x t) b) becomes t[a/x] = t[b/x], which we
    // prove by congruence over the structure of t.
    Node lam = res[0].getOperator();
    Node body = convert(lam[1]);
    std::vector<Node> vars(lam[0].begin(), lam[0].end());
    std::vector<Node> as, bs;
    std::vector<std::shared_ptr<ProofNode>> pfs;
    for (const std::shared_ptr<ProofNode>& c : cs)
    {
      Node eq = c->getResult();
      as.push_back(convert(eq[0]));
      bs.push_back(convert(eq[1]));
      pfs.push_back(convertProof(c));
    }
    if (!d_failed)
    {
      std::unordered_map<Node, std::shared_ptr<ProofNode>> ccache;
      ret = proveCongSubst(body, vars, as, bs, pfs, ccache);
    }
  }
  else if (r == ProofRule::THEORY_REWRITE
           && rewriter::getRewriteRule(args[0], prid)
           && prid == ProofRewriteRule::BETA_REDUCE)
  {
    Node nres = convert(res);
    if (nres[0] == nres[1])
    {
      ret = mk(ProofRule::REFL, {}, {nres[0]}, nres);
    }
    else
    {
      Trace("eo-dfe") << "...beta reduce not refl " << nres << std::endl;
      d_failed = true;
    }
  }
  else
  {
    // generic: convert children, arguments and the conclusion
    bool changed = false;
    std::vector<std::shared_ptr<ProofNode>> ncs;
    for (const std::shared_ptr<ProofNode>& c : cs)
    {
      std::shared_ptr<ProofNode> nc = convertProof(c);
      changed = changed || nc != c;
      ncs.push_back(nc);
    }
    std::vector<Node> nargs;
    for (const Node& a : args)
    {
      Node na = convert(a);
      changed = changed || na != a;
      nargs.push_back(na);
    }
    Node nres = convert(res);
    changed = changed || nres != res;
    if (!changed)
    {
      ret = pn;
    }
    else if (r != ProofRule::ASSUME && nres.getKind() == Kind::EQUAL
             && nres[0] == nres[1])
    {
      // the conclusion became trivial after beta-reduction
      ret = mk(ProofRule::REFL, {}, {nres[0]}, nres);
    }
    else
    {
      ret = mk(r, ncs, nargs, nres);
    }
  }
  if (ret == nullptr || d_failed)
  {
    d_failed = true;
    ret = pn;
  }
  d_pcache[pn.get()] = ret;
  return ret;
}

std::shared_ptr<ProofNode> EoDefineFunElim::process(
    std::shared_ptr<ProofNode> pf, ProofScopeMode psm)
{
  if (psm == ProofScopeMode::NONE)
  {
    return nullptr;
  }
  std::shared_ptr<ProofNode> dscope;
  std::shared_ptr<ProofNode> ascope;
  if (psm == ProofScopeMode::UNIFIED)
  {
    ascope = pf;
  }
  else
  {
    dscope = pf;
    ascope = pf->getChildren()[0];
  }
  if (ascope->getRule() != ProofRule::SCOPE
      || (dscope != nullptr && dscope->getRule() != ProofRule::SCOPE))
  {
    return nullptr;
  }
  const std::vector<Node>& defs =
      dscope != nullptr ? dscope->getArguments() : ascope->getArguments();
  for (const Node& d : defs)
  {
    if (d.getKind() == Kind::EQUAL && d[1].getKind() == Kind::LAMBDA
        && d[0].isVar())
    {
      d_defSyms.insert(d[0]);
    }
  }
  if (d_defSyms.empty())
  {
    return nullptr;
  }
  std::shared_ptr<ProofNode> body = convertProof(ascope->getChildren()[0]);
  if (d_failed)
  {
    return nullptr;
  }
  std::vector<Node> newAsserts;
  for (const Node& a : ascope->getArguments())
  {
    newAsserts.push_back(convert(a));
  }
  std::shared_ptr<ProofNode> ret;
  if (dscope == nullptr)
  {
    ret = mk(ProofRule::SCOPE, {body}, newAsserts, Node::null());
  }
  else
  {
    // definitions that are not converted remain as definitions, the
    // converted ones are now assertions
    std::vector<Node> newDefs;
    for (const Node& d : defs)
    {
      if (isDefEq(d))
      {
        newAsserts.push_back(convert(d));
      }
      else
      {
        newDefs.push_back(d);
      }
    }
    std::shared_ptr<ProofNode> as =
        mk(ProofRule::SCOPE, {body}, newAsserts, Node::null());
    if (d_failed)
    {
      return nullptr;
    }
    ret = mk(ProofRule::SCOPE, {as}, newDefs, Node::null());
  }
  if (d_failed)
  {
    return nullptr;
  }
  return ret;
}

}  // namespace proof
}  // namespace cvc5::internal
