/*********************                                                        */
/*! \file ho_extension.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Mathias Preiner
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Implementation of the higher-order extension of TheoryUF.
 **
 **/

#include "theory/uf/ho_extension.h"

#include "expr/node_algorithm.h"
#include "options/uf_options.h"
#include "theory/theory_model.h"
#include "theory/uf/theory_uf_rewriter.h"

using namespace std;
using namespace CVC4::kind;

namespace CVC4 {
namespace theory {
namespace uf {

HoExtension::HoExtension(TheoryState& state, TheoryInferenceManager& im)
    : d_state(state),
      d_im(im),
      d_extensionality(state.getUserContext()),
      d_uf_std_skolem(state.getUserContext())
{
  d_true = NodeManager::currentNM()->mkConst(true);
}

Node HoExtension::expandDefinition(Node node)
{
  // convert HO_APPLY to APPLY_UF if fully applied
  if (node[0].getType().getNumChildren() == 2)
  {
    Trace("uf-ho") << "uf-ho : expanding definition : " << node << std::endl;
    Node ret = getApplyUfForHoApply(node);
    Trace("uf-ho") << "uf-ho : expandDefinition : " << node << " to " << ret
                   << std::endl;
    return ret;
  }
  return node;
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
  for (unsigned i = 0, nargs = argTypes.size(); i < nargs; i++)
  {
    Node k =
        nm->mkSkolem("k", argTypes[i], "skolem created for extensionality.");
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
    d_im.lemma(lem);
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
  if (!TheoryUfRewriter::canUseAsApplyUfOperator(f))
  {
    NodeNodeMap::const_iterator itus = d_uf_std_skolem.find(f);
    if (itus == d_uf_std_skolem.end())
    {
      std::unordered_set<Node, NodeHashFunction> fvs;
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
        new_f = nm->mkSkolem("app_uf", nft);
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
        new_f = nm->mkSkolem("app_uf", f.getType());
        lem = new_f.eqNode(f);
      }
      Trace("uf-ho-lemma")
          << "uf-ho-lemma : Skolem definition for apply-conversion : " << lem
          << std::endl;
      d_im.lemma(lem);
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
  eq::EqualityEngine* ee = d_state.getEqualityEngine();
  NodeManager* nm = NodeManager::currentNM();
  unsigned num_lemmas = 0;
  bool isCollectModel = (m != nullptr);
  Trace("uf-ho") << "HoExtension::checkExtensionality, collectModel="
                 << isCollectModel << "..." << std::endl;
  std::map<TypeNode, std::vector<Node> > func_eqcs;
  eq::EqClassesIterator eqcs_i = eq::EqClassesIterator(ee);
  while (!eqcs_i.isFinished())
  {
    Node eqc = (*eqcs_i);
    TypeNode tn = eqc.getType();
    if (tn.isFunction())
    {
      // if during collect model, must have an infinite type
      // if not during collect model, must have a finite type
      if (tn.isInterpretedFinite() != isCollectModel)
      {
        func_eqcs[tn].push_back(eqc);
        Trace("uf-ho-debug")
            << "  func eqc : " << tn << " : " << eqc << std::endl;
      }
    }
    ++eqcs_i;
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
        // extensionality to ensure distinctness
        if (!ee->areDisequal(itf->second[j], itf->second[k], false))
        {
          Node deq =
              Rewriter::rewrite(itf->second[j].eqNode(itf->second[k]).negate());
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
              d_im.lemma(lem);
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
    d_im.assertInternalFact(eq, true, PfRule::HO_APP_ENCODE, {}, {n});
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

  if (options::ufHoExt())
  {
    unsigned num_lemmas = 0;

    num_lemmas = checkExtensionality();
    if (num_lemmas > 0)
    {
      Trace("uf-ho") << "...extensionality returned " << num_lemmas
                     << " lemmas." << std::endl;
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
    // For model-building with ufHo, we require that APPLY_UF is always
    // expanded to HO_APPLY. That is, we always expand to a fully applicative
    // encoding during model construction.
    if (!collectModelInfoHoTerm(n, m))
    {
      return false;
    }
  }
  int addedLemmas = checkExtensionality(m);
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
      d_im.lemma(eq);
      return false;
    }
  }
  return true;
}

}  // namespace uf
}  // namespace theory
}  // namespace CVC4
