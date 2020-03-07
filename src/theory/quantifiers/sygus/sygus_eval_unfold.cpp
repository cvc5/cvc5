/*********************                                                        */
/*! \file sygus_eval_unfold.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Implementation of sygus_eval_unfold
 **/

#include "theory/quantifiers/sygus/sygus_eval_unfold.h"

#include "expr/sygus_datatype.h"
#include "options/quantifiers_options.h"
#include "theory/datatypes/theory_datatypes_utils.h"
#include "theory/quantifiers/sygus/term_database_sygus.h"

using namespace std;
using namespace CVC4::kind;
using namespace CVC4::context;

namespace CVC4 {
namespace theory {
namespace quantifiers {

SygusEvalUnfold::SygusEvalUnfold(TermDbSygus* tds) : d_tds(tds) {}

void SygusEvalUnfold::registerEvalTerm(Node n)
{
  Assert(options::sygusEvalUnfold());
  // is this a sygus evaluation function application?
  if (n.getKind() != DT_SYGUS_EVAL)
  {
    return;
  }
  if (d_eval_processed.find(n) != d_eval_processed.end())
  {
    return;
  }
  Trace("sygus-eval-unfold")
      << "SygusEvalUnfold: register eval term : " << n << std::endl;
  d_eval_processed.insert(n);
  TypeNode tn = n[0].getType();
  // since n[0] is an evaluation head, we know tn is a sygus datatype
  Assert(tn.isDatatype());
  const DType& dt = tn.getDType();
  Assert(dt.isSygus());
  if (n[0].getKind() == APPLY_CONSTRUCTOR)
  {
    // constructors should be unfolded and reduced already
    Assert(false);
    return;
  }
  // register this evaluation term with its head
  d_evals[n[0]].push_back(n);
  Node var_list = dt.getSygusVarList();
  d_eval_args[n[0]].push_back(std::vector<Node>());
  for (unsigned j = 1, size = n.getNumChildren(); j < size; j++)
  {
    d_eval_args[n[0]].back().push_back(n[j]);
  }
  Node a = TermDbSygus::getAnchor(n[0]);
  d_subterms[a].insert(n[0]);
}

void SygusEvalUnfold::registerModelValue(Node a,
                                         Node v,
                                         std::vector<Node>& terms,
                                         std::vector<Node>& vals,
                                         std::vector<Node>& exps)
{
  std::map<Node, std::unordered_set<Node, NodeHashFunction> >::iterator its =
      d_subterms.find(a);
  if (its == d_subterms.end())
  {
    return;
  }
  NodeManager* nm = NodeManager::currentNM();
  SygusExplain* sy_exp = d_tds->getExplain();
  Trace("sygus-eval-unfold")
      << "SygusEvalUnfold: " << a << ", has " << its->second.size()
      << " registered subterms." << std::endl;
  for (const Node& n : its->second)
  {
    Trace("sygus-eval-unfold-debug") << "...process : " << n << std::endl;
    std::map<Node, std::vector<std::vector<Node> > >::iterator it =
        d_eval_args.find(n);
    if (it != d_eval_args.end() && !it->second.empty())
    {
      TNode at = a;
      TNode vt = v;
      Node vn = n.substitute(at, vt);
      vn = Rewriter::rewrite(vn);
      unsigned start = d_node_mv_args_proc[n][vn];
      // get explanation in terms of testers
      std::vector<Node> antec_exp;
      sy_exp->getExplanationForEquality(n, vn, antec_exp);
      Node antec =
          antec_exp.size() == 1 ? antec_exp[0] : nm->mkNode(AND, antec_exp);
      // Node antec = n.eqNode( vn );
      TypeNode tn = n.getType();
      // Check if the sygus type has any symbolic constructors. This will
      // impact how the unfolding is computed below.
      SygusTypeInfo& sti = d_tds->getTypeInfo(tn);
      bool hasSymCons = sti.hasSubtermSymbolicCons();
      // n occurs as an evaluation head, thus it has sygus datatype type
      Assert(tn.isDatatype());
      const DType& dt = tn.getDType();
      Assert(dt.isSygus());
      Trace("sygus-eval-unfold")
          << "SygusEvalUnfold: Register model value : " << vn << " for " << n
          << std::endl;
      unsigned curr_size = it->second.size();
      Trace("sygus-eval-unfold")
          << "...it has " << curr_size << " evaluations, already processed "
          << start << "." << std::endl;
      Node bTerm = d_tds->sygusToBuiltin(vn, tn);
      Trace("sygus-eval-unfold") << "Built-in term : " << bTerm << std::endl;
      std::vector<Node> vars;
      Node var_list = dt.getSygusVarList();
      for (const Node& var : var_list)
      {
        vars.push_back(var);
      }
      // evaluation children
      std::vector<Node> eval_children;
      eval_children.push_back(n);
      // for each evaluation
      for (unsigned i = start; i < curr_size; i++)
      {
        Node res;
        Node expn;
        // should we unfold?
        bool do_unfold = false;
        if (options::sygusEvalUnfoldBool())
        {
          Node bTermUse = bTerm;
          if (bTerm.getKind() == APPLY_UF)
          {
            // if the builtin term is non-beta-reduced application of lambda,
            // we look at the body of the lambda.
            Node bTermOp = bTerm.getOperator();
            if (bTermOp.getKind() == LAMBDA)
            {
              bTermUse = bTermOp[0];
            }
          }
          if (bTermUse.getKind() == ITE || bTermUse.getType().isBoolean())
          {
            do_unfold = true;
          }
        }
        if (do_unfold || hasSymCons)
        {
          // note that this is replicated for different values
          std::map<Node, Node> vtm;
          std::vector<Node> exp;
          vtm[n] = vn;
          eval_children.insert(
              eval_children.end(), it->second[i].begin(), it->second[i].end());
          Node eval_fun = nm->mkNode(DT_SYGUS_EVAL, eval_children);
          eval_children.resize(1);
          // If we explicitly asked to unfold, we use single step, otherwise
          // we use multi step.
          res = unfold(eval_fun, vtm, exp, true, !do_unfold);
          Trace("sygus-eval-unfold") << "Unfold returns " << res << std::endl;
          expn = exp.size() == 1 ? exp[0] : nm->mkNode(AND, exp);
        }
        else
        {
          EvalSygusInvarianceTest esit;
          eval_children.insert(
              eval_children.end(), it->second[i].begin(), it->second[i].end());
          Node conj = nm->mkNode(DT_SYGUS_EVAL, eval_children);
          eval_children[0] = vn;
          Node eval_fun = nm->mkNode(DT_SYGUS_EVAL, eval_children);
          res = d_tds->evaluateWithUnfolding(eval_fun);
          Trace("sygus-eval-unfold")
              << "Evaluate with unfolding returns " << res << std::endl;
          esit.init(conj, n, res);
          eval_children.resize(1);
          eval_children[0] = n;

          // evaluate with minimal explanation
          std::vector<Node> mexp;
          sy_exp->getExplanationFor(n, vn, mexp, esit);
          Assert(!mexp.empty());
          expn = mexp.size() == 1 ? mexp[0] : nm->mkNode(AND, mexp);
        }
        Assert(!res.isNull());
        terms.push_back(d_evals[n][i]);
        vals.push_back(res);
        exps.push_back(expn);
        Trace("sygus-eval-unfold")
            << "Conclude : " << d_evals[n][i] << " == " << res << std::endl;
        Trace("sygus-eval-unfold") << "   from " << expn << std::endl;
      }
      d_node_mv_args_proc[n][vn] = curr_size;
    }
  }
}

Node SygusEvalUnfold::unfold(Node en,
                             std::map<Node, Node>& vtm,
                             std::vector<Node>& exp,
                             bool track_exp,
                             bool doRec)
{
  if (en.getKind() != DT_SYGUS_EVAL)
  {
    Assert(en.isConst());
    return en;
  }
  Trace("sygus-eval-unfold-debug")
      << "Unfold : " << en << ", track exp is " << track_exp << ", doRec is "
      << doRec << std::endl;
  Node ev = en[0];
  if (track_exp)
  {
    std::map<Node, Node>::iterator itv = vtm.find(en[0]);
    Assert(itv != vtm.end());
    if (itv != vtm.end())
    {
      ev = itv->second;
    }
    Assert(en[0].getType() == ev.getType());
    Assert(ev.isConst());
  }
  Trace("sygus-eval-unfold-debug")
      << "Unfold model value is : " << ev << std::endl;
  AlwaysAssert(ev.getKind() == APPLY_CONSTRUCTOR);
  std::vector<Node> args;
  for (unsigned i = 1, nchild = en.getNumChildren(); i < nchild; i++)
  {
    args.push_back(en[i]);
  }

  TypeNode headType = en[0].getType();
  NodeManager* nm = NodeManager::currentNM();
  const DType& dt = headType.getDType();
  unsigned i = datatypes::utils::indexOf(ev.getOperator());
  if (track_exp)
  {
    // explanation
    Node ee = nm->mkNode(APPLY_TESTER, dt[i].getTester(), en[0]);
    if (std::find(exp.begin(), exp.end(), ee) == exp.end())
    {
      exp.push_back(ee);
    }
  }
  // if we are a symbolic constructor, unfolding returns the subterm itself
  Node sop = dt[i].getSygusOp();
  if (sop.getAttribute(SygusAnyConstAttribute()))
  {
    Trace("sygus-eval-unfold-debug")
        << "...it is an any-constant constructor" << std::endl;
    Assert(dt[i].getNumArgs() == 1);
    // If the argument to evaluate is itself concrete, then we use its
    // argument; otherwise we return its selector.
    if (en[0].getKind() == APPLY_CONSTRUCTOR)
    {
      Trace("sygus-eval-unfold-debug")
          << "...return (from constructor) " << en[0][0] << std::endl;
      return en[0][0];
    }
    else
    {
      Node ret = nm->mkNode(
          APPLY_SELECTOR_TOTAL, dt[i].getSelectorInternal(headType, 0), en[0]);
      Trace("sygus-eval-unfold-debug")
          << "...return (from constructor) " << ret << std::endl;
      return ret;
    }
  }

  Assert(!dt.isParametric());
  std::map<int, Node> pre;
  for (unsigned j = 0, nargs = dt[i].getNumArgs(); j < nargs; j++)
  {
    std::vector<Node> cc;
    Node s;
    // get the j^th subfield of en
    if (en[0].getKind() == APPLY_CONSTRUCTOR)
    {
      // if it is a concrete constructor application, as an optimization,
      // just return the argument
      s = en[0][j];
    }
    else
    {
      s = nm->mkNode(
          APPLY_SELECTOR_TOTAL, dt[i].getSelectorInternal(headType, j), en[0]);
    }
    cc.push_back(s);
    if (track_exp)
    {
      // update vtm map
      vtm[s] = ev[j];
    }
    cc.insert(cc.end(), args.begin(), args.end());
    Node argj = nm->mkNode(DT_SYGUS_EVAL, cc);
    if (doRec)
    {
      Trace("sygus-eval-unfold-debug") << "Recurse on " << s << std::endl;
      // evaluate recursively
      argj = unfold(argj, vtm, exp, track_exp, doRec);
    }
    pre[j] = argj;
  }
  Node ret = d_tds->mkGeneric(dt, i, pre);
  // apply the appropriate substitution to ret
  ret = datatypes::utils::applySygusArgs(dt, sop, ret, args);
  // rewrite
  ret = Rewriter::rewrite(ret);
  return ret;
}

Node SygusEvalUnfold::unfold(Node en)
{
  std::map<Node, Node> vtm;
  std::vector<Node> exp;
  return unfold(en, vtm, exp, false, false);
}

}  // namespace quantifiers
}  // namespace theory
}  // namespace CVC4
