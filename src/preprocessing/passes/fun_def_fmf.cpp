/*********************                                                        */
/*! \file fun_def_fmf.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Function definition processor for finite model finding
 **/

#include "preprocessing/passes/fun_def_fmf.h"

#include "options/smt_options.h"
#include "proof/proof_manager.h"
#include "theory/quantifiers/quantifiers_attributes.h"
#include "theory/quantifiers/term_database.h"
#include "theory/quantifiers/term_util.h"

using namespace std;
using namespace CVC4::kind;
using namespace CVC4::theory;
using namespace CVC4::theory::quantifiers;

namespace CVC4 {
namespace preprocessing {
namespace passes {

FunDefFmf::FunDefFmf(PreprocessingPassContext* preprocContext)
    : PreprocessingPass(preprocContext, "fun-def-fmf"),
      d_fmfRecFunctionsDefined(nullptr)
{
  d_fmfRecFunctionsDefined =
      new (true) NodeList(preprocContext->getUserContext());
}

FunDefFmf::~FunDefFmf() { d_fmfRecFunctionsDefined->deleteSelf(); }

PreprocessingPassResult FunDefFmf::applyInternal(
    AssertionPipeline* assertionsToPreprocess)
{
  Assert(d_fmfRecFunctionsDefined != nullptr);
  // reset
  d_sorts.clear();
  d_input_arg_inj.clear();
  d_funcs.clear();
  // must carry over current definitions (in case of incremental)
  for (context::CDList<Node>::const_iterator fit =
           d_fmfRecFunctionsDefined->begin();
       fit != d_fmfRecFunctionsDefined->end();
       ++fit)
  {
    Node f = (*fit);
    Assert(d_fmfRecFunctionsAbs.find(f) != d_fmfRecFunctionsAbs.end());
    TypeNode ft = d_fmfRecFunctionsAbs[f];
    d_sorts[f] = ft;
    std::map<Node, std::vector<Node>>::iterator fcit =
        d_fmfRecFunctionsConcrete.find(f);
    Assert(fcit != d_fmfRecFunctionsConcrete.end());
    for (const Node& fcc : fcit->second)
    {
      d_input_arg_inj[f].push_back(fcc);
    }
  }
  process(assertionsToPreprocess);
  // must store new definitions (in case of incremental)
  for (const Node& f : d_funcs)
  {
    d_fmfRecFunctionsAbs[f] = d_sorts[f];
    d_fmfRecFunctionsConcrete[f].clear();
    for (const Node& fcc : d_input_arg_inj[f])
    {
      d_fmfRecFunctionsConcrete[f].push_back(fcc);
    }
    d_fmfRecFunctionsDefined->push_back(f);
  }
  return PreprocessingPassResult::NO_CONFLICT;
}

void FunDefFmf::process(AssertionPipeline* assertionsToPreprocess)
{
  const std::vector<Node>& assertions = assertionsToPreprocess->ref();
  std::vector<int> fd_assertions;
  std::map<int, Node> subs_head;
  // first pass : find defined functions, transform quantifiers
  NodeManager* nm = NodeManager::currentNM();
  for (size_t i = 0, asize = assertions.size(); i < asize; i++)
  {
    Node n = QuantAttributes::getFunDefHead(assertions[i]);
    if (!n.isNull())
    {
      Assert(n.getKind() == APPLY_UF);
      Node f = n.getOperator();

      // check if already defined, if so, throw error
      if (d_sorts.find(f) != d_sorts.end())
      {
        Unhandled() << "Cannot define function " << f << " more than once.";
      }

      Node bd = QuantAttributes::getFunDefBody(assertions[i]);
      Trace("fmf-fun-def-debug")
          << "Process function " << n << ", body = " << bd << std::endl;
      if (!bd.isNull())
      {
        d_funcs.push_back(f);
        bd = nm->mkNode(EQUAL, n, bd);

        // create a sort S that represents the inputs of the function
        std::stringstream ss;
        ss << "I_" << f;
        TypeNode iType = nm->mkSort(ss.str());
        AbsTypeFunDefAttribute atfda;
        iType.setAttribute(atfda, true);
        d_sorts[f] = iType;

        // create functions f1...fn mapping from this sort to concrete elements
        size_t nchildn = n.getNumChildren();
        for (size_t j = 0; j < nchildn; j++)
        {
          TypeNode typ = nm->mkFunctionType(iType, n[j].getType());
          std::stringstream ssf;
          ssf << f << "_arg_" << j;
          d_input_arg_inj[f].push_back(
              nm->mkSkolem(ssf.str(), typ, "op created during fun def fmf"));
        }

        // construct new quantifier forall S. F[f1(S)/x1....fn(S)/xn]
        std::vector<Node> children;
        Node bv = nm->mkBoundVar("?i", iType);
        Node bvl = nm->mkNode(BOUND_VAR_LIST, bv);
        std::vector<Node> subs;
        std::vector<Node> vars;
        for (size_t j = 0; j < nchildn; j++)
        {
          vars.push_back(n[j]);
          subs.push_back(nm->mkNode(APPLY_UF, d_input_arg_inj[f][j], bv));
        }
        bd = bd.substitute(vars.begin(), vars.end(), subs.begin(), subs.end());
        subs_head[i] =
            n.substitute(vars.begin(), vars.end(), subs.begin(), subs.end());

        Trace("fmf-fun-def")
            << "FMF fun def: FUNCTION : rewrite " << assertions[i] << std::endl;
        Trace("fmf-fun-def") << "  to " << std::endl;
        Node new_q = nm->mkNode(FORALL, bvl, bd);
        new_q = Rewriter::rewrite(new_q);
        assertionsToPreprocess->replace(i, new_q);
        Trace("fmf-fun-def") << "  " << assertions[i] << std::endl;
        fd_assertions.push_back(i);
      }
      else
      {
        // can be, e.g. in corner cases forall x. f(x)=f(x), forall x.
        // f(x)=f(x)+1
      }
    }
  }
  // second pass : rewrite assertions
  std::map<int, std::map<Node, Node>> visited;
  std::map<int, std::map<Node, Node>> visited_cons;
  for (size_t i = 0, asize = assertions.size(); i < asize; i++)
  {
    bool is_fd = std::find(fd_assertions.begin(), fd_assertions.end(), i)
                 != fd_assertions.end();
    std::vector<Node> constraints;
    Trace("fmf-fun-def-rewrite")
        << "Rewriting " << assertions[i]
        << ", is function definition = " << is_fd << std::endl;
    Node n = simplifyFormula(assertions[i],
                             true,
                             true,
                             constraints,
                             is_fd ? subs_head[i] : Node::null(),
                             is_fd,
                             visited,
                             visited_cons);
    Assert(constraints.empty());
    if (n != assertions[i])
    {
      n = Rewriter::rewrite(n);
      Trace("fmf-fun-def-rewrite")
          << "FMF fun def : rewrite " << assertions[i] << std::endl;
      Trace("fmf-fun-def-rewrite") << "  to " << std::endl;
      Trace("fmf-fun-def-rewrite") << "  " << n << std::endl;
      assertionsToPreprocess->replace(i, n);
    }
  }
}

Node FunDefFmf::simplifyFormula(
    Node n,
    bool pol,
    bool hasPol,
    std::vector<Node>& constraints,
    Node hd,
    bool is_fun_def,
    std::map<int, std::map<Node, Node>>& visited,
    std::map<int, std::map<Node, Node>>& visited_cons)
{
  Assert(constraints.empty());
  int index = (is_fun_def ? 1 : 0) + 2 * (hasPol ? (pol ? 1 : -1) : 0);
  std::map<Node, Node>::iterator itv = visited[index].find(n);
  if (itv != visited[index].end())
  {
    // constraints.insert( visited_cons[index]
    std::map<Node, Node>::iterator itvc = visited_cons[index].find(n);
    if (itvc != visited_cons[index].end())
    {
      constraints.push_back(itvc->second);
    }
    return itv->second;
  }
  NodeManager* nm = NodeManager::currentNM();
  Node ret;
  Trace("fmf-fun-def-debug2") << "Simplify " << n << " " << pol << " " << hasPol
                              << " " << is_fun_def << std::endl;
  if (n.getKind() == FORALL)
  {
    Node c = simplifyFormula(
        n[1], pol, hasPol, constraints, hd, is_fun_def, visited, visited_cons);
    // append prenex to constraints
    for (unsigned i = 0; i < constraints.size(); i++)
    {
      constraints[i] = nm->mkNode(FORALL, n[0], constraints[i]);
      constraints[i] = Rewriter::rewrite(constraints[i]);
    }
    if (c != n[1])
    {
      ret = nm->mkNode(FORALL, n[0], c);
    }
    else
    {
      ret = n;
    }
  }
  else
  {
    Node nn = n;
    bool isBool = n.getType().isBoolean();
    if (isBool && n.getKind() != APPLY_UF)
    {
      std::vector<Node> children;
      bool childChanged = false;
      // are we at a branch position (not all children are necessarily
      // relevant)?
      bool branch_pos =
          (n.getKind() == ITE || n.getKind() == OR || n.getKind() == AND);
      std::vector<Node> branch_constraints;
      for (unsigned i = 0; i < n.getNumChildren(); i++)
      {
        Node c = n[i];
        // do not process LHS of definition
        if (!is_fun_def || c != hd)
        {
          bool newHasPol;
          bool newPol;
          QuantPhaseReq::getPolarity(n, i, hasPol, pol, newHasPol, newPol);
          // get child constraints
          std::vector<Node> cconstraints;
          c = simplifyFormula(n[i],
                              newPol,
                              newHasPol,
                              cconstraints,
                              hd,
                              false,
                              visited,
                              visited_cons);
          if (branch_pos)
          {
            // if at a branching position, the other constraints don't matter
            // if this is satisfied
            Node bcons = nm->mkAnd(cconstraints);
            branch_constraints.push_back(bcons);
            Trace("fmf-fun-def-debug2") << "Branching constraint at arg " << i
                                        << " is " << bcons << std::endl;
          }
          constraints.insert(
              constraints.end(), cconstraints.begin(), cconstraints.end());
        }
        children.push_back(c);
        childChanged = c != n[i] || childChanged;
      }
      if (childChanged)
      {
        nn = nm->mkNode(n.getKind(), children);
      }
      if (branch_pos && !constraints.empty())
      {
        // if we are at a branching position in the formula, we can
        // minimize recursive constraints on recursively defined predicates if
        // we know one child forces the overall evaluation of this formula.
        Node branch_cond;
        if (n.getKind() == ITE)
        {
          // always care about constraints on the head of the ITE, but only
          // care about one of the children depending on how it evaluates
          branch_cond = nm->mkNode(
              AND,
              branch_constraints[0],
              nm->mkNode(
                  ITE, n[0], branch_constraints[1], branch_constraints[2]));
        }
        else
        {
          // in the default case, we care about all conditions
          branch_cond = nm->mkAnd(constraints);
          for (size_t i = 0, nchild = n.getNumChildren(); i < nchild; i++)
          {
            // if this child holds with forcing polarity (true child of OR or
            // false child of AND), then we only care about its associated
            // recursive conditions
            branch_cond = nm->mkNode(ITE,
                                     (n.getKind() == OR ? n[i] : n[i].negate()),
                                     branch_constraints[i],
                                     branch_cond);
          }
        }
        Trace("fmf-fun-def-debug2")
            << "Made branching condition " << branch_cond << std::endl;
        constraints.clear();
        constraints.push_back(branch_cond);
      }
    }
    else
    {
      // simplify term
      std::map<Node, Node> visitedT;
      getConstraints(n, constraints, visitedT);
    }
    if (!constraints.empty() && isBool && hasPol)
    {
      // conjoin with current
      Node cons = nm->mkAnd(constraints);
      if (pol)
      {
        ret = nm->mkNode(AND, nn, cons);
      }
      else
      {
        ret = nm->mkNode(OR, nn, cons.negate());
      }
      Trace("fmf-fun-def-debug2")
          << "Add constraint to obtain " << ret << std::endl;
      constraints.clear();
    }
    else
    {
      ret = nn;
    }
  }
  if (!constraints.empty())
  {
    Node cons;
    // flatten to AND node for the purposes of caching
    if (constraints.size() > 1)
    {
      cons = nm->mkNode(AND, constraints);
      cons = Rewriter::rewrite(cons);
      constraints.clear();
      constraints.push_back(cons);
    }
    else
    {
      cons = constraints[0];
    }
    visited_cons[index][n] = cons;
    Assert(constraints.size() == 1 && constraints[0] == cons);
  }
  visited[index][n] = ret;
  return ret;
}

void FunDefFmf::getConstraints(Node n,
                               std::vector<Node>& constraints,
                               std::map<Node, Node>& visited)
{
  std::map<Node, Node>::iterator itv = visited.find(n);
  if (itv != visited.end())
  {
    // already visited
    if (!itv->second.isNull())
    {
      // add the cached constraint if it does not already occur
      if (std::find(constraints.begin(), constraints.end(), itv->second)
          == constraints.end())
      {
        constraints.push_back(itv->second);
      }
    }
    return;
  }
  visited[n] = Node::null();
  std::vector<Node> currConstraints;
  NodeManager* nm = NodeManager::currentNM();
  if (n.getKind() == ITE)
  {
    // collect constraints for the condition
    getConstraints(n[0], currConstraints, visited);
    // collect constraints for each branch
    Node cs[2];
    for (unsigned i = 0; i < 2; i++)
    {
      std::vector<Node> ccons;
      getConstraints(n[i + 1], ccons, visited);
      cs[i] = nm->mkAnd(ccons);
    }
    if (!cs[0].isConst() || !cs[1].isConst())
    {
      Node itec = nm->mkNode(ITE, n[0], cs[0], cs[1]);
      currConstraints.push_back(itec);
      Trace("fmf-fun-def-debug")
          << "---> add constraint " << itec << " for " << n << std::endl;
    }
  }
  else
  {
    if (n.getKind() == APPLY_UF)
    {
      // check if f is defined, if so, we must enforce domain constraints for
      // this f-application
      Node f = n.getOperator();
      std::map<Node, TypeNode>::iterator it = d_sorts.find(f);
      if (it != d_sorts.end())
      {
        // create existential
        Node z = nm->mkBoundVar("?z", it->second);
        Node bvl = nm->mkNode(BOUND_VAR_LIST, z);
        std::vector<Node> children;
        for (unsigned j = 0, size = n.getNumChildren(); j < size; j++)
        {
          Node uz = nm->mkNode(APPLY_UF, d_input_arg_inj[f][j], z);
          children.push_back(uz.eqNode(n[j]));
        }
        Node bd = nm->mkAnd(children);
        bd = bd.negate();
        Node ex = nm->mkNode(FORALL, bvl, bd);
        ex = ex.negate();
        currConstraints.push_back(ex);
        Trace("fmf-fun-def-debug")
            << "---> add constraint " << ex << " for " << n << std::endl;
      }
    }
    for (const Node& cn : n)
    {
      getConstraints(cn, currConstraints, visited);
    }
  }
  // set the visited cache
  if (!currConstraints.empty())
  {
    Node finalc = nm->mkAnd(currConstraints);
    visited[n] = finalc;
    // add to constraints
    getConstraints(n, constraints, visited);
  }
}

}  // namespace passes
}  // namespace preprocessing
}  // namespace CVC4
