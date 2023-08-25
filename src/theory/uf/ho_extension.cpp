/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Gereon Kremer, Andres Noetzli
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Implementation of the higher-order extension of TheoryUF.
 */

#include "theory/uf/ho_extension.h"

#include "expr/node_algorithm.h"
#include "expr/skolem_manager.h"
#include "options/uf_options.h"
#include "theory/theory_model.h"
#include "theory/uf/function_const.h"
#include "theory/uf/lambda_lift.h"
#include "theory/uf/theory_uf_rewriter.h"

using namespace std;
using namespace cvc5::internal::kind;

namespace cvc5::internal {
namespace theory {
namespace uf {

HoExtension::HoExtension(Env& env,
                         TheoryState& state,
                         TheoryInferenceManager& im,
                         LambdaLift& ll)
    : EnvObj(env),
      d_state(state),
      d_im(im),
      d_ll(ll),
      d_extensionality(userContext()),
      d_cachedLemmas(userContext()),
      d_uf_std_skolem(userContext())
{
  d_true = NodeManager::currentNM()->mkConst(true);
}

TrustNode HoExtension::ppRewrite(Node node, std::vector<SkolemLemma>& lems)
{
  Kind k = node.getKind();
  if (k == HO_APPLY)
  {
    // convert HO_APPLY to APPLY_UF if fully applied
    if (node[0].getType().getNumChildren() == 2)
    {
      Trace("uf-ho") << "uf-ho : expanding definition : " << node << std::endl;
      Node ret = getApplyUfForHoApply(node);
      Trace("uf-ho") << "uf-ho : ppRewrite : " << node << " to " << ret
                     << std::endl;
      return TrustNode::mkTrustRewrite(node, ret);
    }
    // partial beta reduction
    // f ---> (lambda ((x Int) (y Int)) s[x, y]) then (@ f t) is preprocessed
    // to (lambda ((y Int)) s[t, y]).
    if (options().uf.ufHoLazyLambdaLift)
    {
      Node op = node[0];
      Node opl = d_ll.getLambdaFor(op);
      if (!opl.isNull())
      {
        NodeManager* nm = NodeManager::currentNM();
        Node app = nm->mkNode(HO_APPLY, opl, node[1]);
        app = rewrite(app);
        Trace("uf-lazy-ll")
            << "Partial beta reduce: " << node << " -> " << app << std::endl;
        return TrustNode::mkTrustRewrite(node, app, nullptr);
      }
    }
  }
  else if (k == APPLY_UF)
  {
    // Say (lambda ((x Int)) t[x]) occurs in the input. We replace this
    // by k during ppRewrite. In the following, if we see (k s), we replace
    // it by t[s]. This maintains the invariant that the *only* occurences
    // of k are as arguments to other functions; k is not applied
    // in any preprocessed constraints.
    if (options().uf.ufHoLazyLambdaLift)
    {
      // if an application of the lambda lifted function, do beta reduction
      // immediately
      Node op = node.getOperator();
      Node opl = d_ll.getLambdaFor(op);
      if (!opl.isNull())
      {
        Assert(opl.getKind() == LAMBDA);
        std::vector<Node> args(node.begin(), node.end());
        Node app = d_ll.betaReduce(opl, args);
        Trace("uf-lazy-ll")
            << "Beta reduce: " << node << " -> " << app << std::endl;
        return TrustNode::mkTrustRewrite(node, app, nullptr);
      }
    }
  }
  else if (k == kind::LAMBDA || k == kind::FUNCTION_ARRAY_CONST)
  {
    Trace("uf-lazy-ll") << "Preprocess lambda: " << node << std::endl;
    TrustNode skTrn = d_ll.ppRewrite(node, lems);
    Trace("uf-lazy-ll") << "...return " << skTrn.getNode() << std::endl;
    return skTrn;
  }
  return TrustNode::null();
}

Node HoExtension::getExtensionalityDeq(TNode deq, bool isCached)
{
  Assert(deq.getKind() == NOT && deq[0].getKind() == EQUAL);
  Assert(deq[0][0].getType().isFunction());
  if (isCached)
  {
    std::map<Node, Node>::iterator it = d_extensionality_deq.find(deq);
    if (it != d_extensionality_deq.end())
    {
      return it->second;
    }
  }
  TypeNode tn = deq[0][0].getType();
  std::vector<TypeNode> argTypes = tn.getArgTypes();
  std::vector<Node> skolems;
  NodeManager* nm = NodeManager::currentNM();
  SkolemManager* sm = nm->getSkolemManager();
  for (unsigned i = 0, nargs = argTypes.size(); i < nargs; i++)
  {
    Node k = sm->mkDummySkolem(
        "k", argTypes[i], "skolem created for extensionality.");
    skolems.push_back(k);
  }
  Node t[2];
  for (unsigned i = 0; i < 2; i++)
  {
    std::vector<Node> children;
    Node curr = deq[0][i];
    while (curr.getKind() == HO_APPLY)
    {
      children.push_back(curr[1]);
      curr = curr[0];
    }
    children.push_back(curr);
    std::reverse(children.begin(), children.end());
    children.insert(children.end(), skolems.begin(), skolems.end());
    t[i] = nm->mkNode(APPLY_UF, children);
  }
  Node conc = t[0].eqNode(t[1]).negate();
  if (isCached)
  {
    d_extensionality_deq[deq] = conc;
  }
  return conc;
}

unsigned HoExtension::applyExtensionality(TNode deq)
{
  Assert(deq.getKind() == NOT && deq[0].getKind() == EQUAL);
  Assert(deq[0][0].getType().isFunction());
  // apply extensionality
  if (d_extensionality.find(deq) == d_extensionality.end())
  {
    d_extensionality.insert(deq);
    Node conc = getExtensionalityDeq(deq);
    Node lem = NodeManager::currentNM()->mkNode(OR, deq[0], conc);
    Trace("uf-ho-lemma") << "uf-ho-lemma : extensionality : " << lem
                         << std::endl;
    d_im.lemma(lem, InferenceId::UF_HO_EXTENSIONALITY);
    return 1;
  }
  return 0;
}

Node HoExtension::getApplyUfForHoApply(Node node)
{
  Assert(node[0].getType().getNumChildren() == 2);
  std::vector<TNode> args;
  Node f = TheoryUfRewriter::decomposeHoApply(node, args, true);
  Node new_f = f;
  NodeManager* nm = NodeManager::currentNM();
  SkolemManager* sm = nm->getSkolemManager();
  if (!TheoryUfRewriter::canUseAsApplyUfOperator(f))
  {
    NodeNodeMap::const_iterator itus = d_uf_std_skolem.find(f);
    if (itus == d_uf_std_skolem.end())
    {
      std::unordered_set<Node> fvs;
      expr::getFreeVariables(f, fvs);
      Node lem;
      if (!fvs.empty())
      {
        std::vector<TypeNode> newTypes;
        std::vector<Node> vs;
        std::vector<Node> nvs;
        for (const Node& v : fvs)
        {
          TypeNode vt = v.getType();
          newTypes.push_back(vt);
          Node nv = nm->mkBoundVar(vt);
          vs.push_back(v);
          nvs.push_back(nv);
        }
        TypeNode ft = f.getType();
        std::vector<TypeNode> argTypes = ft.getArgTypes();
        TypeNode rangeType = ft.getRangeType();

        newTypes.insert(newTypes.end(), argTypes.begin(), argTypes.end());
        TypeNode nft = nm->mkFunctionType(newTypes, rangeType);
        new_f = sm->mkDummySkolem("app_uf", nft);
        for (const Node& v : vs)
        {
          new_f = nm->mkNode(HO_APPLY, new_f, v);
        }
        Assert(new_f.getType() == f.getType());
        Node eq = new_f.eqNode(f);
        Node seq = eq.substitute(vs.begin(), vs.end(), nvs.begin(), nvs.end());
        lem = nm->mkNode(
            FORALL, nm->mkNode(BOUND_VAR_LIST, nvs), seq);
      }
      else
      {
        // introduce skolem to make a standard APPLY_UF
        new_f = sm->mkDummySkolem("app_uf", f.getType());
        lem = new_f.eqNode(f);
      }
      Trace("uf-ho-lemma")
          << "uf-ho-lemma : Skolem definition for apply-conversion : " << lem
          << std::endl;
      d_im.lemma(lem, InferenceId::UF_HO_APP_CONV_SKOLEM);
      d_uf_std_skolem[f] = new_f;
    }
    else
    {
      new_f = (*itus).second;
    }
    // unroll the HO_APPLY, adding to the first argument position
    // Note arguments in the vector args begin at position 1.
    while (new_f.getKind() == HO_APPLY)
    {
      args.insert(args.begin() + 1, new_f[1]);
      new_f = new_f[0];
    }
  }
  Assert(TheoryUfRewriter::canUseAsApplyUfOperator(new_f));
  args[0] = new_f;
  Node ret = nm->mkNode(APPLY_UF, args);
  Assert(ret.getType() == node.getType());
  return ret;
}

unsigned HoExtension::checkExtensionality(TheoryModel* m)
{
  // if we are in collect model info, we require looking at the model's
  // equality engine, so that we only consider "relevant" (see
  // Theory::computeRelevantTerms) function terms.
  eq::EqualityEngine* ee =
      m != nullptr ? m->getEqualityEngine() : d_state.getEqualityEngine();
  NodeManager* nm = NodeManager::currentNM();
  unsigned num_lemmas = 0;
  bool isCollectModel = (m != nullptr);
  Trace("uf-ho") << "HoExtension::checkExtensionality, collectModel="
                 << isCollectModel << "..." << std::endl;
  std::map<TypeNode, std::vector<Node> > func_eqcs;
  eq::EqClassesIterator eqcs_i = eq::EqClassesIterator(ee);
  bool hasFunctions = false;
  while (!eqcs_i.isFinished())
  {
    Node eqc = (*eqcs_i);
    TypeNode tn = eqc.getType();
    if (tn.isFunction() && d_lambdaEqc.find(eqc) == d_lambdaEqc.end())
    {
      hasFunctions = true;
      // if during collect model, must have an infinite type
      // if not during collect model, must have a finite type
      if (d_env.isFiniteType(tn) != isCollectModel)
      {
        func_eqcs[tn].push_back(eqc);
        Trace("uf-ho-debug")
            << "  func eqc : " << tn << " : " << eqc << std::endl;
      }
    }
    ++eqcs_i;
  }
  if (!options().uf.ufHoExt)
  {
    // we are not applying extensionality, thus we are incomplete if functions
    // are present
    if (hasFunctions)
    {
      d_im.setModelUnsound(IncompleteId::UF_HO_EXT_DISABLED);
    }
    return 0;
  }

  for (std::map<TypeNode, std::vector<Node> >::iterator itf = func_eqcs.begin();
       itf != func_eqcs.end();
       ++itf)
  {
    for (unsigned j = 0, sizej = itf->second.size(); j < sizej; j++)
    {
      for (unsigned k = (j + 1), sizek = itf->second.size(); k < sizek; k++)
      {
        // if these equivalence classes are not explicitly disequal, do
        // extensionality to ensure distinctness. Notice that we always use
        // the (local) equality engine for this check via the state, since the
        // model's equality engine does not store any disequalities. This is
        // an optimization to introduce fewer equalities during model
        // construction, since we know such disequalities have already been
        // witness via assertions.
        if (!d_state.areDisequal(itf->second[j], itf->second[k]))
        {
          Node deq = rewrite(itf->second[j].eqNode(itf->second[k]).negate());
          // either add to model, or add lemma
          if (isCollectModel)
          {
            // Add extentionality disequality to the model.
            // It is important that we construct new (unconstrained) variables
            // k here, so that we do not generate any inconsistencies.
            Node edeq = getExtensionalityDeq(deq, false);
            Assert(edeq.getKind() == NOT && edeq[0].getKind() == EQUAL);
            // introducing terms, must add required constraints, e.g. to
            // force equalities between APPLY_UF and HO_APPLY terms
            for (unsigned r = 0; r < 2; r++)
            {
              if (!collectModelInfoHoTerm(edeq[0][r], m))
              {
                return 1;
              }
            }
            Trace("uf-ho-debug")
                << "Add extensionality deq to model : " << edeq << std::endl;
            if (!m->assertEquality(edeq[0][0], edeq[0][1], false))
            {
              Node eq = edeq[0][0].eqNode(edeq[0][1]);
              Node lem = nm->mkNode(OR, deq.negate(), eq);
              Trace("uf-ho") << "HoExtension: cmi extensionality lemma " << lem
                             << std::endl;
              d_im.lemma(lem, InferenceId::UF_HO_MODEL_EXTENSIONALITY);
              return 1;
            }
          }
          else
          {
            // apply extensionality lemma
            num_lemmas += applyExtensionality(deq);
          }
        }
      }
    }
  }
  return num_lemmas;
}

unsigned HoExtension::applyAppCompletion(TNode n)
{
  Assert(n.getKind() == APPLY_UF);

  eq::EqualityEngine* ee = d_state.getEqualityEngine();
  // must expand into APPLY_HO version if not there already
  Node ret = TheoryUfRewriter::getHoApplyForApplyUf(n);
  if (!ee->hasTerm(ret) || !ee->areEqual(ret, n))
  {
    Node eq = n.eqNode(ret);
    Trace("uf-ho-lemma") << "uf-ho-lemma : infer, by apply-expand : " << eq
                         << std::endl;
    d_im.assertInternalFact(eq,
                            true,
                            InferenceId::UF_HO_APP_ENCODE,
                            PfRule::HO_APP_ENCODE,
                            {},
                            {n});
    return 1;
  }
  Trace("uf-ho-debug") << "    ...already have " << ret << " == " << n << "."
                       << std::endl;
  return 0;
}

unsigned HoExtension::checkAppCompletion()
{
  Trace("uf-ho") << "HoExtension::checkApplyCompletion..." << std::endl;
  // compute the operators that are relevant (those for which an HO_APPLY exist)
  std::set<TNode> rlvOp;
  eq::EqualityEngine* ee = d_state.getEqualityEngine();
  eq::EqClassesIterator eqcs_i = eq::EqClassesIterator(ee);
  std::map<TNode, std::vector<Node> > apply_uf;
  while (!eqcs_i.isFinished())
  {
    Node eqc = (*eqcs_i);
    Trace("uf-ho-debug") << "  apply completion : visit eqc " << eqc
                         << std::endl;
    eq::EqClassIterator eqc_i = eq::EqClassIterator(eqc, ee);
    while (!eqc_i.isFinished())
    {
      Node n = *eqc_i;
      if (n.getKind() == APPLY_UF || n.getKind() == HO_APPLY)
      {
        int curr_sum = 0;
        std::map<TNode, bool> curr_rops;
        if (n.getKind() == APPLY_UF)
        {
          TNode rop = ee->getRepresentative(n.getOperator());
          if (rlvOp.find(rop) != rlvOp.end())
          {
            // try if its operator is relevant
            curr_sum = applyAppCompletion(n);
            if (curr_sum > 0)
            {
              return curr_sum;
            }
          }
          else
          {
            // add to pending list
            apply_uf[rop].push_back(n);
          }
          // Arguments are also relevant operators.
          // It might be possible include fewer terms here, see #1115.
          for (unsigned k = 0; k < n.getNumChildren(); k++)
          {
            if (n[k].getType().isFunction())
            {
              TNode rop2 = ee->getRepresentative(n[k]);
              curr_rops[rop2] = true;
            }
          }
        }
        else
        {
          Assert(n.getKind() == HO_APPLY);
          TNode rop = ee->getRepresentative(n[0]);
          curr_rops[rop] = true;
        }
        for (std::map<TNode, bool>::iterator itc = curr_rops.begin();
             itc != curr_rops.end();
             ++itc)
        {
          TNode rop = itc->first;
          if (rlvOp.find(rop) == rlvOp.end())
          {
            rlvOp.insert(rop);
            // now, try each pending APPLY_UF for this operator
            std::map<TNode, std::vector<Node> >::iterator itu =
                apply_uf.find(rop);
            if (itu != apply_uf.end())
            {
              for (unsigned j = 0, size = itu->second.size(); j < size; j++)
              {
                curr_sum = applyAppCompletion(itu->second[j]);
                if (curr_sum > 0)
                {
                  return curr_sum;
                }
              }
            }
          }
        }
      }
      ++eqc_i;
    }
    ++eqcs_i;
  }
  return 0;
}

unsigned HoExtension::checkLazyLambda()
{
  if (!options().uf.ufHoLazyLambdaLift)
  {
    // no lambdas are lazily lifted
    return 0;
  }
  Trace("uf-ho") << "HoExtension::checkLazyLambda..." << std::endl;
  NodeManager* nm = NodeManager::currentNM();
  unsigned numLemmas = 0;
  d_lambdaEqc.clear();
  eq::EqualityEngine* ee = d_state.getEqualityEngine();
  eq::EqClassesIterator eqcs_i = eq::EqClassesIterator(ee);
  // normal functions equated to lambda functions
  std::unordered_set<Node> normalEqFuns;
  // mapping from functions to terms
  while (!eqcs_i.isFinished())
  {
    Node eqc = (*eqcs_i);
    ++eqcs_i;
    if (!eqc.getType().isFunction())
    {
      continue;
    }
    eq::EqClassIterator eqc_i = eq::EqClassIterator(eqc, ee);
    Node lamRep;  // the first lambda function we encounter in the equivalence
                  // class
    Node lamRepLam;
    std::unordered_set<Node> normalEqFunWait;
    while (!eqc_i.isFinished())
    {
      Node n = *eqc_i;
      ++eqc_i;
      Node lam = d_ll.getLambdaFor(n);
      if (lam.isNull())
      {
        if (!lamRep.isNull())
        {
          // if we are equal to a lambda function, we must beta-reduce
          // applications of this
          normalEqFuns.insert(n);
        }
        else
        {
          // waiting to see if there is a lambda function in this equivalence
          // class
          normalEqFunWait.insert(n);
        }
      }
      else if (lamRep.isNull())
      {
        // there is a lambda function in this equivalence class
        lamRep = n;
        lamRepLam = lam;
        // must consider all normal functions we've seen so far
        normalEqFuns.insert(normalEqFunWait.begin(), normalEqFunWait.end());
        normalEqFunWait.clear();
      }
      else
      {
        // two lambda functions are in same equivalence class
        Node f = lamRep < n ? lamRep : n;
        Node g = lamRep < n ? n : lamRep;
        Trace("uf-ho-debug") << "  found equivalent lambda functions " << f
                             << " and " << g << std::endl;
        Node flam = lamRep < n ? lamRepLam : lam;
        Assert(!flam.isNull() && flam.getKind() == LAMBDA);
        Node lhs = flam[1];
        Node glam = lamRep < n ? lam : lamRepLam;
        Trace("uf-ho-debug")
            << "  lambda are " << flam << " and " << glam << std::endl;
        std::vector<Node> args(flam[0].begin(), flam[0].end());
        Node rhs = d_ll.betaReduce(glam, args);
        Node univ = nm->mkNode(FORALL, flam[0], lhs.eqNode(rhs));
        // f = g => forall x. reduce(lambda(f)(x)) = reduce(lambda(g)(x))
        //
        // For example, if f -> lambda z. z+1, g -> lambda y. y+3, this
        // will infer: f = g => forall x. x+1 = x+3, which simplifies to
        // f != g.
        Node lem = nm->mkNode(IMPLIES, f.eqNode(g), univ);
        if (cacheLemma(lem))
        {
          d_im.lemma(lem, InferenceId::UF_HO_LAMBDA_UNIV_EQ);
          numLemmas++;
        }
      }
    }
    if (!lamRep.isNull())
    {
      d_lambdaEqc[eqc] = lamRep;
    }
  }
  Trace("uf-ho-debug")
      << "  found " << normalEqFuns.size()
      << " ordinary functions that are equal to lambda functions" << std::endl;
  if (normalEqFuns.empty())
  {
    return numLemmas;
  }
  // if we have normal functions that are equal to lambda functions, go back
  // and ensure they are mapped properly
  // mapping from functions to terms
  eq::EqClassesIterator eqcs_i2 = eq::EqClassesIterator(ee);
  while (!eqcs_i2.isFinished())
  {
    Node eqc = (*eqcs_i2);
    ++eqcs_i2;
    Trace("uf-ho-debug") << "Check equivalence class " << eqc << std::endl;
    eq::EqClassIterator eqc_i = eq::EqClassIterator(eqc, ee);
    while (!eqc_i.isFinished())
    {
      Node n = *eqc_i;
      ++eqc_i;
      Trace("uf-ho-debug") << "Check term " << n << std::endl;
      Node op;
      Kind k = n.getKind();
      std::vector<Node> args;
      if (k == APPLY_UF)
      {
        op = n.getOperator();
        args.insert(args.end(), n.begin(), n.end());
      }
      else if (k == HO_APPLY)
      {
        op = n[0];
        args.push_back(n[1]);
      }
      else
      {
        continue;
      }
      if (normalEqFuns.find(op) == normalEqFuns.end())
      {
        continue;
      }
      Trace("uf-ho-debug") << "  found relevant ordinary application " << n
                           << std::endl;
      Assert(ee->hasTerm(op));
      Node r = ee->getRepresentative(op);
      Assert(d_lambdaEqc.find(r) != d_lambdaEqc.end());
      Node lf = d_lambdaEqc[r];
      Node lam = d_ll.getLambdaFor(lf);
      Assert(!lam.isNull() && lam.getKind() == LAMBDA);
      // a normal function g equal to a lambda, say f --> lambda(f)
      // need to infer f = g => g(t) = f(t) for all terms g(t)
      // that occur in the equality engine.
      Node premise = op.eqNode(lf);
      args.insert(args.begin(), lam);
      Node rhs = nm->mkNode(n.getKind(), args);
      rhs = rewrite(rhs);
      Node conc = n.eqNode(rhs);
      Node lem = nm->mkNode(IMPLIES, premise, conc);
      if (cacheLemma(lem))
      {
        d_im.lemma(lem, InferenceId::UF_HO_LAMBDA_APP_REDUCE);
        numLemmas++;
      }
    }
  }
  return numLemmas;
}

unsigned HoExtension::check()
{
  Trace("uf-ho") << "HoExtension::checkHigherOrder..." << std::endl;

  // infer new facts based on apply completion until fixed point
  unsigned num_facts;
  do
  {
    num_facts = checkAppCompletion();
    if (d_state.isInConflict())
    {
      Trace("uf-ho") << "...conflict during app-completion." << std::endl;
      return 1;
    }
  } while (num_facts > 0);

  // Apply extensionality, lazy lambda schemas in order. We make lazy lambda
  // handling come last as it may introduce quantifiers.
  for (size_t i = 0; i < 2; i++)
  {
    unsigned num_lemmas = 0;
    // apply the schema
    switch (i)
    {
      case 0: num_lemmas = checkExtensionality(); break;
      case 1: num_lemmas = checkLazyLambda(); break;
      default: break;
    }
    // finish if we added lemmas
    if (num_lemmas > 0)
    {
      Trace("uf-ho") << "...returned " << num_lemmas << " lemmas." << std::endl;
      return num_lemmas;
    }
  }

  Trace("uf-ho") << "...finished check higher order." << std::endl;

  return 0;
}

bool HoExtension::collectModelInfoHo(TheoryModel* m,
                                     const std::set<Node>& termSet)
{
  for (std::set<Node>::iterator it = termSet.begin(); it != termSet.end(); ++it)
  {
    Node n = *it;
    // For model-building with higher-order, we require that APPLY_UF is always
    // expanded to HO_APPLY. That is, we always expand to a fully applicative
    // encoding during model construction.
    if (!collectModelInfoHoTerm(n, m))
    {
      return false;
    }
  }
  // We apply an explicit extensionality technique for asserting
  // disequalities to the model to ensure that function values are distinct
  // in the curried HO_APPLY version of model construction. This is a
  // non-standard alternative to using a type enumerator over function
  // values to assign unique values.
  int addedLemmas = checkExtensionality(m);
  // for equivalence classes that we know to assign a lambda directly
  for (const std::pair<const Node, Node>& p : d_lambdaEqc)
  {
    Node lam = d_ll.getLambdaFor(p.second);
    Assert(!lam.isNull());
    m->assertEquality(p.second, lam, true);
    m->assertSkeleton(lam);
    // assign it as the function definition for all variables in this class
    m->assignFunctionDefinition(p.second, lam);
  }
  return addedLemmas == 0;
}

bool HoExtension::collectModelInfoHoTerm(Node n, TheoryModel* m)
{
  if (n.getKind() == APPLY_UF)
  {
    Node hn = TheoryUfRewriter::getHoApplyForApplyUf(n);
    if (!m->assertEquality(n, hn, true))
    {
      Node eq = n.eqNode(hn);
      Trace("uf-ho") << "HoExtension: cmi app completion lemma " << eq
                     << std::endl;
      d_im.lemma(eq, InferenceId::UF_HO_MODEL_APP_ENCODE);
      return false;
    }
  }
  return true;
}

bool HoExtension::cacheLemma(TNode lem)
{
  Node rewritten = rewrite(lem);
  if (d_cachedLemmas.find(rewritten) != d_cachedLemmas.end())
  {
    return false;
  }
  d_cachedLemmas.insert(rewritten);
  return true;
}

}  // namespace uf
}  // namespace theory
}  // namespace cvc5::internal
