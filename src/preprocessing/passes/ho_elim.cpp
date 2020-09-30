/*********************                                                        */
/*! \file ho_elim.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief The HoElim preprocessing pass
 **
 ** Eliminates higher-order constraints.
 **/

#include "preprocessing/passes/ho_elim.h"

#include "expr/node_algorithm.h"
#include "options/quantifiers_options.h"
#include "theory/rewriter.h"
#include "theory/uf/theory_uf_rewriter.h"

using namespace CVC4::kind;

namespace CVC4 {
namespace preprocessing {
namespace passes {

HoElim::HoElim(PreprocessingPassContext* preprocContext)
    : PreprocessingPass(preprocContext, "ho-elim"){};

Node HoElim::eliminateLambdaComplete(Node n, std::map<Node, Node>& newLambda)
{
  NodeManager* nm = NodeManager::currentNM();
  std::unordered_map<TNode, Node, TNodeHashFunction>::iterator it;
  std::vector<TNode> visit;
  TNode cur;
  visit.push_back(n);
  do
  {
    cur = visit.back();
    visit.pop_back();
    it = d_visited.find(cur);

    if (it == d_visited.end())
    {
      if (cur.getKind() == LAMBDA)
      {
        Trace("ho-elim-ll") << "Lambda lift: " << cur << std::endl;
        // must also get free variables in lambda
        std::vector<Node> lvars;
        std::vector<TypeNode> ftypes;
        std::unordered_set<Node, NodeHashFunction> fvs;
        expr::getFreeVariables(cur, fvs);
        std::vector<Node> nvars;
        std::vector<Node> vars;
        Node sbd = cur[1];
        if (!fvs.empty())
        {
          Trace("ho-elim-ll")
              << "Has " << fvs.size() << " free variables" << std::endl;
          for (const Node& v : fvs)
          {
            TypeNode vt = v.getType();
            ftypes.push_back(vt);
            Node vs = nm->mkBoundVar(vt);
            vars.push_back(v);
            nvars.push_back(vs);
            lvars.push_back(vs);
          }
          sbd = sbd.substitute(
              vars.begin(), vars.end(), nvars.begin(), nvars.end());
        }
        for (const Node& bv : cur[0])
        {
          TypeNode bvt = bv.getType();
          ftypes.push_back(bvt);
          lvars.push_back(bv);
        }
        Node nlambda = cur;
        if (!fvs.empty())
        {
          nlambda = nm->mkNode(LAMBDA, nm->mkNode(BOUND_VAR_LIST, lvars), sbd);
          Trace("ho-elim-ll")
              << "...new lambda definition: " << nlambda << std::endl;
        }
        TypeNode rangeType = cur.getType().getRangeType();
        TypeNode nft = nm->mkFunctionType(ftypes, rangeType);
        Node nf = nm->mkSkolem("ll", nft);
        Trace("ho-elim-ll")
            << "...introduce: " << nf << " of type " << nft << std::endl;
        newLambda[nf] = nlambda;
        Assert(nf.getType() == nlambda.getType());
        if (!vars.empty())
        {
          for (const Node& v : vars)
          {
            nf = nm->mkNode(HO_APPLY, nf, v);
          }
          Trace("ho-elim-ll") << "...partial application: " << nf << std::endl;
        }
        d_visited[cur] = nf;
        Trace("ho-elim-ll") << "...return types : " << nf.getType() << " "
                            << cur.getType() << std::endl;
        Assert(nf.getType() == cur.getType());
      }
      else
      {
        d_visited[cur] = Node::null();
        visit.push_back(cur);
        for (const Node& cn : cur)
        {
          visit.push_back(cn);
        }
      }
    }
    else if (it->second.isNull())
    {
      Node ret = cur;
      bool childChanged = false;
      std::vector<Node> children;
      if (cur.getMetaKind() == metakind::PARAMETERIZED)
      {
        children.push_back(cur.getOperator());
      }
      for (const Node& cn : cur)
      {
        it = d_visited.find(cn);
        Assert(it != d_visited.end());
        Assert(!it->second.isNull());
        childChanged = childChanged || cn != it->second;
        children.push_back(it->second);
      }
      if (childChanged)
      {
        ret = nm->mkNode(cur.getKind(), children);
      }
      d_visited[cur] = ret;
    }
  } while (!visit.empty());
  Assert(d_visited.find(n) != d_visited.end());
  Assert(!d_visited.find(n)->second.isNull());
  return d_visited[n];
}

Node HoElim::eliminateHo(Node n)
{
  Trace("ho-elim-assert") << "Ho-elim assertion: " << n << std::endl;
  NodeManager* nm = NodeManager::currentNM();
  std::unordered_map<TNode, Node, TNodeHashFunction>::iterator it;
  std::map<Node, Node> preReplace;
  std::map<Node, Node>::iterator itr;
  std::vector<TNode> visit;
  TNode cur;
  visit.push_back(n);
  do
  {
    cur = visit.back();
    visit.pop_back();
    it = d_visited.find(cur);
    Trace("ho-elim-visit") << "Process: " << cur << std::endl;

    if (it == d_visited.end())
    {
      TypeNode tn = cur.getType();
      // lambdas are already eliminated by now
      Assert(cur.getKind() != LAMBDA);
      if (tn.isFunction())
      {
        d_funTypes.insert(tn);
      }
      if (cur.isVar())
      {
        Node ret = cur;
        if (options::hoElim())
        {
          if (tn.isFunction())
          {
            TypeNode ut = getUSort(tn);
            if (cur.getKind() == BOUND_VARIABLE)
            {
              ret = nm->mkBoundVar(ut);
            }
            else
            {
              ret = nm->mkSkolem("k", ut);
            }
            // must get the ho apply to ensure extensionality is applied
            Node hoa = getHoApplyUf(tn);
            Trace("ho-elim-visit") << "Hoa is " << hoa << std::endl;
          }
        }
        d_visited[cur] = ret;
      }
      else
      {
        d_visited[cur] = Node::null();
        if (cur.getKind() == APPLY_UF && options::hoElim())
        {
          Node op = cur.getOperator();
          // convert apply uf with variable arguments eagerly to ho apply
          // chains, so they are processed uniformly.
          visit.push_back(cur);
          Node newCur = theory::uf::TheoryUfRewriter::getHoApplyForApplyUf(cur);
          preReplace[cur] = newCur;
          cur = newCur;
          d_visited[cur] = Node::null();
        }
        visit.push_back(cur);
        for (const Node& cn : cur)
        {
          visit.push_back(cn);
        }
      }
    }
    else if (it->second.isNull())
    {
      Node ret = cur;
      itr = preReplace.find(cur);
      if (itr != preReplace.end())
      {
        Trace("ho-elim-visit")
            << "return (pre-repl): " << d_visited[itr->second] << std::endl;
        d_visited[cur] = d_visited[itr->second];
      }
      else
      {
        bool childChanged = false;
        std::vector<Node> children;
        std::vector<TypeNode> childrent;
        bool typeChanged = false;
        for (const Node& cn : ret)
        {
          it = d_visited.find(cn);
          Assert(it != d_visited.end());
          Assert(!it->second.isNull());
          childChanged = childChanged || cn != it->second;
          children.push_back(it->second);
          TypeNode ct = it->second.getType();
          childrent.push_back(ct);
          typeChanged = typeChanged || ct != cn.getType();
        }
        if (ret.getMetaKind() == metakind::PARAMETERIZED)
        {
          // child of an argument changed type, must change type
          Node op = ret.getOperator();
          Node retOp = op;
          Trace("ho-elim-visit")
              << "Process op " << op << ", typeChanged = " << typeChanged
              << std::endl;
          if (typeChanged)
          {
            std::unordered_map<TNode, Node, TNodeHashFunction>::iterator ito =
                d_visited_op.find(op);
            if (ito == d_visited_op.end())
            {
              Assert(!childrent.empty());
              TypeNode newFType = nm->mkFunctionType(childrent, cur.getType());
              retOp = nm->mkSkolem("rf", newFType);
              d_visited_op[op] = retOp;
            }
            else
            {
              retOp = ito->second;
            }
          }
          children.insert(children.begin(), retOp);
        }
        // process ho apply
        if (ret.getKind() == HO_APPLY && options::hoElim())
        {
          TypeNode tnr = ret.getType();
          tnr = getUSort(tnr);
          Node hoa =
              getHoApplyUf(children[0].getType(), children[1].getType(), tnr);
          std::vector<Node> hchildren;
          hchildren.push_back(hoa);
          hchildren.push_back(children[0]);
          hchildren.push_back(children[1]);
          ret = nm->mkNode(APPLY_UF, hchildren);
        }
        else if (childChanged)
        {
          ret = nm->mkNode(ret.getKind(), children);
        }
        Trace("ho-elim-visit") << "return (pre-repl): " << ret << std::endl;
        d_visited[cur] = ret;
      }
    }
  } while (!visit.empty());
  Assert(d_visited.find(n) != d_visited.end());
  Assert(!d_visited.find(n)->second.isNull());
  Trace("ho-elim-assert") << "...got : " << d_visited[n] << std::endl;
  return d_visited[n];
}

PreprocessingPassResult HoElim::applyInternal(
    AssertionPipeline* assertionsToPreprocess)
{
  // step [1]: apply lambda lifting to eliminate all lambdas
  NodeManager* nm = NodeManager::currentNM();
  std::vector<Node> axioms;
  std::map<Node, Node> newLambda;
  for (unsigned i = 0, size = assertionsToPreprocess->size(); i < size; ++i)
  {
    Node prev = (*assertionsToPreprocess)[i];
    Node res = eliminateLambdaComplete(prev, newLambda);
    if (res != prev)
    {
      res = theory::Rewriter::rewrite(res);
      Assert(!expr::hasFreeVar(res));
      assertionsToPreprocess->replace(i, res);
    }
  }
  // do lambda lifting on new lambda definitions
  // this will do fixed point to eliminate lambdas within lambda lifting axioms.
  while (!newLambda.empty())
  {
    std::map<Node, Node> lproc = newLambda;
    newLambda.clear();
    for (const std::pair<Node, Node>& l : lproc)
    {
      Node lambda = l.second;
      std::vector<Node> vars;
      std::vector<Node> nvars;
      for (const Node& v : lambda[0])
      {
        Node bv = nm->mkBoundVar(v.getType());
        vars.push_back(v);
        nvars.push_back(bv);
      }

      Node bd = lambda[1].substitute(
          vars.begin(), vars.end(), nvars.begin(), nvars.end());
      Node bvl = nm->mkNode(BOUND_VAR_LIST, nvars);

      nvars.insert(nvars.begin(), l.first);
      Node curr = nm->mkNode(APPLY_UF, nvars);

      Node llfax = nm->mkNode(FORALL, bvl, curr.eqNode(bd));
      Trace("ho-elim-ax") << "Lambda lifting axiom (pre-elim) " << llfax
                          << " for " << lambda << std::endl;
      Assert(!expr::hasFreeVar(llfax));
      Node llfaxe = eliminateLambdaComplete(llfax, newLambda);
      Trace("ho-elim-ax") << "Lambda lifting axiom " << llfaxe << " for "
                          << lambda << std::endl;
      axioms.push_back(llfaxe);
    }
  }

  d_visited.clear();
  // add lambda lifting axioms as a conjunction to the first assertion
  if (!axioms.empty())
  {
    Node orig = (*assertionsToPreprocess)[0];
    axioms.push_back(orig);
    Node conj = nm->mkNode(AND, axioms);
    conj = theory::Rewriter::rewrite(conj);
    Assert(!expr::hasFreeVar(conj));
    assertionsToPreprocess->replace(0, conj);
  }
  axioms.clear();

  // step [2]: eliminate all higher-order constraints
  for (unsigned i = 0, size = assertionsToPreprocess->size(); i < size; ++i)
  {
    Node prev = (*assertionsToPreprocess)[i];
    Node res = eliminateHo(prev);
    if (res != prev)
    {
      res = theory::Rewriter::rewrite(res);
      Assert(!expr::hasFreeVar(res));
      assertionsToPreprocess->replace(i, res);
    }
  }
  // extensionality: process all function types
  for (const TypeNode& ftn : d_funTypes)
  {
    if (options::hoElim())
    {
      Node h = getHoApplyUf(ftn);
      Trace("ho-elim-ax") << "Make extensionality for " << h << std::endl;
      TypeNode ft = h.getType();
      TypeNode uf = getUSort(ft[0]);
      TypeNode ut = getUSort(ft[1]);
      // extensionality
      Node x = nm->mkBoundVar("x", uf);
      Node y = nm->mkBoundVar("y", uf);
      Node z = nm->mkBoundVar("z", ut);
      Node eq =
          nm->mkNode(APPLY_UF, h, x, z).eqNode(nm->mkNode(APPLY_UF, h, y, z));
      Node antec = nm->mkNode(FORALL, nm->mkNode(BOUND_VAR_LIST, z), eq);
      Node conc = x.eqNode(y);
      Node ax = nm->mkNode(FORALL,
                           nm->mkNode(BOUND_VAR_LIST, x, y),
                           nm->mkNode(OR, antec.negate(), conc));
      axioms.push_back(ax);
      Trace("ho-elim-ax") << "...ext axiom : " << ax << std::endl;
      // Make the "store" axiom, which asserts for every function, there
      // exists another function that acts like the "store" operator for
      // arrays, e.g. it is the same function with one I/O pair updated.
      // Without this axiom, the translation is model unsound.
      if (options::hoElimStoreAx())
      {
        Node u = nm->mkBoundVar("u", uf);
        Node v = nm->mkBoundVar("v", uf);
        Node i = nm->mkBoundVar("i", ut);
        Node ii = nm->mkBoundVar("ii", ut);
        Node huii = nm->mkNode(APPLY_UF, h, u, ii);
        Node e = nm->mkBoundVar("e", huii.getType());
        Node store = nm->mkNode(
            FORALL,
            nm->mkNode(BOUND_VAR_LIST, u, e, i),
            nm->mkNode(EXISTS,
                       nm->mkNode(BOUND_VAR_LIST, v),
                       nm->mkNode(FORALL,
                                  nm->mkNode(BOUND_VAR_LIST, ii),
                                  nm->mkNode(APPLY_UF, h, v, ii)
                                      .eqNode(nm->mkNode(
                                          ITE, ii.eqNode(i), e, huii)))));
        axioms.push_back(store);
        Trace("ho-elim-ax") << "...store axiom : " << store << std::endl;
      }
    }
    else if (options::hoElimStoreAx())
    {
      Node u = nm->mkBoundVar("u", ftn);
      Node v = nm->mkBoundVar("v", ftn);
      std::vector<TypeNode> argTypes = ftn.getArgTypes();
      Node i = nm->mkBoundVar("i", argTypes[0]);
      Node ii = nm->mkBoundVar("ii", argTypes[0]);
      Node huii = nm->mkNode(HO_APPLY, u, ii);
      Node e = nm->mkBoundVar("e", huii.getType());
      Node store = nm->mkNode(
          FORALL,
          nm->mkNode(BOUND_VAR_LIST, u, e, i),
          nm->mkNode(
              EXISTS,
              nm->mkNode(BOUND_VAR_LIST, v),
              nm->mkNode(FORALL,
                         nm->mkNode(BOUND_VAR_LIST, ii),
                         nm->mkNode(HO_APPLY, v, ii)
                             .eqNode(nm->mkNode(ITE, ii.eqNode(i), e, huii)))));
      axioms.push_back(store);
      Trace("ho-elim-ax") << "...store (ho_apply) axiom : " << store
                          << std::endl;
    }
  }
  // add new axioms as a conjunction to the first assertion
  if (!axioms.empty())
  {
    Node orig = (*assertionsToPreprocess)[0];
    axioms.push_back(orig);
    Node conj = nm->mkNode(AND, axioms);
    conj = theory::Rewriter::rewrite(conj);
    Assert(!expr::hasFreeVar(conj));
    assertionsToPreprocess->replace(0, conj);
  }

  return PreprocessingPassResult::NO_CONFLICT;
}

Node HoElim::getHoApplyUf(TypeNode tn)
{
  TypeNode tnu = getUSort(tn);
  TypeNode rangeType = tn.getRangeType();
  std::vector<TypeNode> argTypes = tn.getArgTypes();
  TypeNode tna = getUSort(argTypes[0]);

  TypeNode tr = rangeType;
  if (argTypes.size() > 1)
  {
    std::vector<TypeNode> remArgTypes;
    remArgTypes.insert(remArgTypes.end(), argTypes.begin() + 1, argTypes.end());
    tr = NodeManager::currentNM()->mkFunctionType(remArgTypes, tr);
  }
  TypeNode tnr = getUSort(tr);

  return getHoApplyUf(tnu, tna, tnr);
}

Node HoElim::getHoApplyUf(TypeNode tnf, TypeNode tna, TypeNode tnr)
{
  std::map<TypeNode, Node>::iterator it = d_hoApplyUf.find(tnf);
  if (it == d_hoApplyUf.end())
  {
    NodeManager* nm = NodeManager::currentNM();

    std::vector<TypeNode> hoTypeArgs;
    hoTypeArgs.push_back(tnf);
    hoTypeArgs.push_back(tna);
    TypeNode tnh = nm->mkFunctionType(hoTypeArgs, tnr);
    Node k = NodeManager::currentNM()->mkSkolem("ho", tnh);
    d_hoApplyUf[tnf] = k;
    return k;
  }
  return it->second;
}

TypeNode HoElim::getUSort(TypeNode tn)
{
  if (!tn.isFunction())
  {
    return tn;
  }
  std::map<TypeNode, TypeNode>::iterator it = d_ftypeMap.find(tn);
  if (it == d_ftypeMap.end())
  {
    // flatten function arguments
    std::vector<TypeNode> argTypes = tn.getArgTypes();
    TypeNode rangeType = tn.getRangeType();
    bool typeChanged = false;
    for (unsigned i = 0; i < argTypes.size(); i++)
    {
      if (argTypes[i].isFunction())
      {
        argTypes[i] = getUSort(argTypes[i]);
        typeChanged = true;
      }
    }
    TypeNode s;
    if (typeChanged)
    {
      TypeNode ntn =
          NodeManager::currentNM()->mkFunctionType(argTypes, rangeType);
      s = getUSort(ntn);
    }
    else
    {
      std::stringstream ss;
      ss << "u_" << tn;
      s = NodeManager::currentNM()->mkSort(ss.str());
    }
    d_ftypeMap[tn] = s;
    return s;
  }
  return it->second;
}

}  // namespace passes
}  // namespace preprocessing
}  // namespace CVC4
