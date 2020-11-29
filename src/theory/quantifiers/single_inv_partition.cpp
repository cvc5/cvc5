/*********************                                                        */
/*! \file single_inv_partition.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Mathias Preiner, Morgan Deters
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief utility for processing single invocation synthesis conjectures
 **
 **/
#include "theory/quantifiers/single_inv_partition.h"

#include "expr/node_algorithm.h"
#include "theory/quantifiers/term_util.h"

using namespace CVC4;
using namespace CVC4::kind;
using namespace std;

namespace CVC4 {
namespace theory {
namespace quantifiers {

bool SingleInvocationPartition::init(Node n)
{
  // first, get types of arguments for functions
  std::vector<TypeNode> typs;
  std::map<Node, bool> visited;
  std::vector<Node> funcs;
  if (inferArgTypes(n, typs, visited))
  {
    return init(funcs, typs, n, false);
  }
  else
  {
    Trace("si-prt") << "Could not infer argument types." << std::endl;
    return false;
  }
}

Node SingleInvocationPartition::getFirstOrderVariableForFunction(Node f) const
{
  std::map<Node, Node>::const_iterator it = d_func_fo_var.find(f);
  if (it != d_func_fo_var.end())
  {
    return it->second;
  }
  return Node::null();
}

Node SingleInvocationPartition::getFunctionForFirstOrderVariable(Node v) const
{
  std::map<Node, Node>::const_iterator it = d_fo_var_to_func.find(v);
  if (it != d_fo_var_to_func.end())
  {
    return it->second;
  }
  return Node::null();
}

Node SingleInvocationPartition::getFunctionInvocationFor(Node f) const
{
  std::map<Node, Node>::const_iterator it = d_func_inv.find(f);
  if (it != d_func_inv.end())
  {
    return it->second;
  }
  return Node::null();
}

void SingleInvocationPartition::getFunctionVariables(
    std::vector<Node>& fvars) const
{
  fvars.insert(fvars.end(), d_func_vars.begin(), d_func_vars.end());
}

void SingleInvocationPartition::getFunctions(std::vector<Node>& fs) const
{
  fs.insert(fs.end(), d_all_funcs.begin(), d_all_funcs.end());
}

void SingleInvocationPartition::getSingleInvocationVariables(
    std::vector<Node>& sivars) const
{
  sivars.insert(sivars.end(), d_si_vars.begin(), d_si_vars.end());
}

void SingleInvocationPartition::getAllVariables(std::vector<Node>& vars) const
{
  vars.insert(vars.end(), d_all_vars.begin(), d_all_vars.end());
}

// gets the argument type list for the first APPLY_UF we see
bool SingleInvocationPartition::inferArgTypes(Node n,
                                              std::vector<TypeNode>& typs,
                                              std::map<Node, bool>& visited)
{
  if (visited.find(n) == visited.end())
  {
    visited[n] = true;
    if (n.getKind() != FORALL)
    {
      if (n.getKind() == APPLY_UF)
      {
        for (unsigned i = 0; i < n.getNumChildren(); i++)
        {
          typs.push_back(n[i].getType());
        }
        return true;
      }
      else
      {
        for (unsigned i = 0; i < n.getNumChildren(); i++)
        {
          if (inferArgTypes(n[i], typs, visited))
          {
            return true;
          }
        }
      }
    }
  }
  return false;
}

bool SingleInvocationPartition::init(std::vector<Node>& funcs, Node n)
{
  Trace("si-prt") << "Initialize with " << funcs.size() << " input functions ("
                  << funcs << ")..." << std::endl;
  std::vector<TypeNode> typs;
  if (!funcs.empty())
  {
    TypeNode tn0 = funcs[0].getType();
    if (tn0.getNumChildren() > 0)
    {
      for (unsigned i = 0, nargs = tn0.getNumChildren() - 1; i < nargs; i++)
      {
        typs.push_back(tn0[i]);
      }
    }
    for (unsigned i = 1, size = funcs.size(); i < size; i++)
    {
      TypeNode tni = funcs[i].getType();
      if (tni.getNumChildren() != tn0.getNumChildren())
      {
        // can't anti-skolemize functions of different sort
        Trace("si-prt") << "...type mismatch" << std::endl;
        return false;
      }
      else if (tni.getNumChildren() > 0)
      {
        for (unsigned j = 0, nargs = tni.getNumChildren() - 1; j < nargs; j++)
        {
          if (tni[j] != typs[j])
          {
            Trace("si-prt") << "...argument type mismatch" << std::endl;
            return false;
          }
        }
      }
    }
  }
  Trace("si-prt") << "#types = " << typs.size() << std::endl;
  return init(funcs, typs, n, true);
}

bool SingleInvocationPartition::init(std::vector<Node>& funcs,
                                     std::vector<TypeNode>& typs,
                                     Node n,
                                     bool has_funcs)
{
  Assert(d_arg_types.empty());
  Assert(d_input_funcs.empty());
  Assert(d_si_vars.empty());
  NodeManager* nm = NodeManager::currentNM();
  d_has_input_funcs = has_funcs;
  d_arg_types.insert(d_arg_types.end(), typs.begin(), typs.end());
  d_input_funcs.insert(d_input_funcs.end(), funcs.begin(), funcs.end());
  Trace("si-prt") << "Initialize..." << std::endl;
  for (unsigned j = 0; j < d_arg_types.size(); j++)
  {
    std::stringstream ss;
    ss << "s_" << j;
    Node si_v = nm->mkBoundVar(ss.str(), d_arg_types[j]);
    d_si_vars.push_back(si_v);
  }
  Assert(d_si_vars.size() == d_arg_types.size());
  for (const Node& inf : d_input_funcs)
  {
    Node sk = nm->mkSkolem("_sik", inf.getType());
    d_input_func_sks.push_back(sk);
  }
  Trace("si-prt") << "SingleInvocationPartition::process " << n << std::endl;
  Trace("si-prt") << "Get conjuncts..." << std::endl;
  std::vector<Node> conj;
  if (collectConjuncts(n, true, conj))
  {
    Trace("si-prt") << "...success." << std::endl;
    for (unsigned i = 0; i < conj.size(); i++)
    {
      std::vector<Node> si_terms;
      std::vector<Node> si_subs;
      Trace("si-prt") << "Process conjunct : " << conj[i] << std::endl;
      // do DER on conjunct
      // Must avoid eliminating the first-order input functions in the
      // getQuantSimplify step below. We use a substitution to avoid this.
      // This makes it so that e.g. the synthesis conjecture:
      //   exists f. f!=0 ^ P
      // is not rewritten to exists f. (f=0 => false) ^ P and subsquently
      // rewritten to exists f. false ^ P by the elimination f -> 0.
      Node cr = conj[i].substitute(d_input_funcs.begin(),
                                   d_input_funcs.end(),
                                   d_input_func_sks.begin(),
                                   d_input_func_sks.end());
      cr = TermUtil::getQuantSimplify(cr);
      cr = cr.substitute(d_input_func_sks.begin(),
                         d_input_func_sks.end(),
                         d_input_funcs.begin(),
                         d_input_funcs.end());
      if (cr != conj[i])
      {
        Trace("si-prt-debug") << "...rewritten to " << cr << std::endl;
      }
      std::map<Node, bool> visited;
      // functions to arguments
      std::vector<Node> args;
      std::vector<Node> terms;
      std::vector<Node> subs;
      bool singleInvocation = true;
      bool ngroundSingleInvocation = false;
      if (processConjunct(cr, visited, args, terms, subs))
      {
        for (unsigned j = 0; j < terms.size(); j++)
        {
          si_terms.push_back(subs[j]);
          Node op = subs[j].hasOperator() ? subs[j].getOperator() : subs[j];
          Assert(d_func_fo_var.find(op) != d_func_fo_var.end());
          si_subs.push_back(d_func_fo_var[op]);
        }
        std::map<Node, Node> subs_map;
        std::map<Node, Node> subs_map_rev;
        // normalize the invocations
        if (!terms.empty())
        {
          Assert(terms.size() == subs.size());
          cr = cr.substitute(
              terms.begin(), terms.end(), subs.begin(), subs.end());
        }
        std::vector<Node> children;
        children.push_back(cr);
        terms.clear();
        subs.clear();
        Trace("si-prt") << "...single invocation, with arguments: "
                        << std::endl;
        for (unsigned j = 0; j < args.size(); j++)
        {
          Trace("si-prt") << args[j] << " ";
          if (args[j].getKind() == BOUND_VARIABLE
              && std::find(terms.begin(), terms.end(), args[j]) == terms.end())
          {
            terms.push_back(args[j]);
            subs.push_back(d_si_vars[j]);
          }
          else
          {
            children.push_back(d_si_vars[j].eqNode(args[j]).negate());
          }
        }
        Trace("si-prt") << std::endl;
        cr = children.size() == 1
                 ? children[0]
                 : NodeManager::currentNM()->mkNode(OR, children);
        Assert(terms.size() == subs.size());
        cr =
            cr.substitute(terms.begin(), terms.end(), subs.begin(), subs.end());
        Trace("si-prt-debug") << "...normalized invocations to " << cr
                              << std::endl;
        // now must check if it has other bound variables
        std::unordered_set<Node, NodeHashFunction> fvs;
        expr::getFreeVariables(cr, fvs);
        // bound variables must be contained in the single invocation variables
        for (const Node& bv : fvs)
        {
          if (std::find(d_si_vars.begin(), d_si_vars.end(), bv)
              == d_si_vars.end())
          {
            // getFreeVariables also collects functions in the rare case that
            // we are synthesizing a function with 0 arguments, take this into
            // account here.
            if (std::find(d_input_funcs.begin(), d_input_funcs.end(), bv)
                == d_input_funcs.end())
            {
              Trace("si-prt")
                  << "...not ground single invocation." << std::endl;
              ngroundSingleInvocation = true;
              singleInvocation = false;
            }
          }
        }
        if (singleInvocation)
        {
          Trace("si-prt") << "...ground single invocation" << std::endl;
        }
      }
      else
      {
        Trace("si-prt") << "...not single invocation." << std::endl;
        singleInvocation = false;
        // rename bound variables with maximal overlap with si_vars
        std::unordered_set<Node, NodeHashFunction> fvs;
        expr::getFreeVariables(cr, fvs);
        std::vector<Node> termsNs;
        std::vector<Node> subsNs;
        for (const Node& v : fvs)
        {
          TypeNode tn = v.getType();
          Trace("si-prt-debug")
              << "Fit bound var: " << v << " with si." << std::endl;
          for (unsigned k = 0; k < d_si_vars.size(); k++)
          {
            if (tn == d_arg_types[k])
            {
              if (std::find(subsNs.begin(), subsNs.end(), d_si_vars[k])
                  == subsNs.end())
              {
                termsNs.push_back(v);
                subsNs.push_back(d_si_vars[k]);
                Trace("si-prt-debug") << "  ...use " << d_si_vars[k]
                                      << std::endl;
                break;
              }
            }
          }
        }
        Assert(termsNs.size() == subsNs.size());
        cr = cr.substitute(
            termsNs.begin(), termsNs.end(), subsNs.begin(), subsNs.end());
      }
      cr = Rewriter::rewrite(cr);
      Trace("si-prt") << ".....got si=" << singleInvocation
                      << ", result : " << cr << std::endl;
      d_conjuncts[2].push_back(cr);
      std::unordered_set<Node, NodeHashFunction> fvs;
      expr::getFreeVariables(cr, fvs);
      d_all_vars.insert(fvs.begin(), fvs.end());
      if (singleInvocation)
      {
        // replace with single invocation formulation
        Assert(si_terms.size() == si_subs.size());
        cr = cr.substitute(
            si_terms.begin(), si_terms.end(), si_subs.begin(), si_subs.end());
        cr = Rewriter::rewrite(cr);
        Trace("si-prt") << ".....si version=" << cr << std::endl;
        d_conjuncts[0].push_back(cr);
      }
      else
      {
        d_conjuncts[1].push_back(cr);
        if (ngroundSingleInvocation)
        {
          d_conjuncts[3].push_back(cr);
        }
      }
    }
  }
  else
  {
    Trace("si-prt") << "...failed." << std::endl;
    return false;
  }
  return true;
}

bool SingleInvocationPartition::collectConjuncts(Node n,
                                                 bool pol,
                                                 std::vector<Node>& conj)
{
  if ((!pol && n.getKind() == OR) || (pol && n.getKind() == AND))
  {
    for (unsigned i = 0; i < n.getNumChildren(); i++)
    {
      if (!collectConjuncts(n[i], pol, conj))
      {
        return false;
      }
    }
  }
  else if (n.getKind() == NOT)
  {
    return collectConjuncts(n[0], !pol, conj);
  }
  else if (n.getKind() == FORALL)
  {
    return false;
  }
  else
  {
    if (!pol)
    {
      n = TermUtil::simpleNegate(n);
    }
    Trace("si-prt") << "Conjunct : " << n << std::endl;
    conj.push_back(n);
  }
  return true;
}

bool SingleInvocationPartition::processConjunct(Node n,
                                                std::map<Node, bool>& visited,
                                                std::vector<Node>& args,
                                                std::vector<Node>& terms,
                                                std::vector<Node>& subs)
{
  std::map<Node, bool>::iterator it = visited.find(n);
  if (it != visited.end())
  {
    return true;
  }
  else
  {
    bool ret = true;
    for (unsigned i = 0; i < n.getNumChildren(); i++)
    {
      if (!processConjunct(n[i], visited, args, terms, subs))
      {
        ret = false;
      }
    }
    if (ret)
    {
      Node f;
      bool success = false;
      if (d_has_input_funcs)
      {
        f = n.hasOperator() ? n.getOperator() : n;
        if (std::find(d_input_funcs.begin(), d_input_funcs.end(), f)
            != d_input_funcs.end())
        {
          success = true;
        }
      }
      else
      {
        if (n.getKind() == kind::APPLY_UF)
        {
          f = n.getOperator();
          success = true;
        }
      }
      if (success)
      {
        if (std::find(terms.begin(), terms.end(), n) == terms.end())
        {
          // check if it matches the type requirement
          if (isAntiSkolemizableType(f))
          {
            if (args.empty())
            {
              // record arguments
              for (unsigned i = 0; i < n.getNumChildren(); i++)
              {
                args.push_back(n[i]);
              }
            }
            else
            {
              // arguments must be the same as those already recorded
              for (unsigned i = 0; i < n.getNumChildren(); i++)
              {
                if (args[i] != n[i])
                {
                  Trace("si-prt-debug") << "...bad invocation : " << n
                                        << " at arg " << i << "." << std::endl;
                  ret = false;
                  break;
                }
              }
            }
            if (ret)
            {
              terms.push_back(n);
              subs.push_back(d_func_inv[f]);
            }
          }
          else
          {
            Trace("si-prt-debug") << "... " << f << " is a bad operator."
                                  << std::endl;
            ret = false;
          }
        }
      }
    }
    //}
    visited[n] = ret;
    return ret;
  }
}

bool SingleInvocationPartition::isAntiSkolemizableType(Node f)
{
  std::map<Node, bool>::iterator it = d_funcs.find(f);
  if (it != d_funcs.end())
  {
    return it->second;
  }
  else
  {
    TypeNode tn = f.getType();
    bool ret = false;
    if (((tn.isFunction() && tn.getNumChildren() == d_arg_types.size() + 1)
         || (d_arg_types.empty() && tn.getNumChildren() == 0)))
    {
      ret = true;
      std::vector<Node> children;
      children.push_back(f);
      // TODO: permutations of arguments
      for (unsigned i = 0; i < d_arg_types.size(); i++)
      {
        children.push_back(d_si_vars[i]);
        if (tn[i] != d_arg_types[i])
        {
          ret = false;
          break;
        }
      }
      if (ret)
      {
        Node t;
        if (children.size() > 1)
        {
          t = NodeManager::currentNM()->mkNode(kind::APPLY_UF, children);
        }
        else
        {
          t = children[0];
        }
        d_func_inv[f] = t;
        std::stringstream ss;
        ss << "F_" << f;
        TypeNode rt;
        if (d_arg_types.empty())
        {
          rt = tn;
        }
        else
        {
          rt = tn.getRangeType();
        }
        Node v = NodeManager::currentNM()->mkBoundVar(ss.str(), rt);
        d_func_fo_var[f] = v;
        d_fo_var_to_func[v] = f;
        d_func_vars.push_back(v);
        d_all_funcs.push_back(f);
      }
    }
    d_funcs[f] = ret;
    return ret;
  }
}

Node SingleInvocationPartition::getConjunct(int index)
{
  return d_conjuncts[index].empty() ? NodeManager::currentNM()->mkConst(true)
                                    : (d_conjuncts[index].size() == 1
                                           ? d_conjuncts[index][0]
                                           : NodeManager::currentNM()->mkNode(
                                                 AND, d_conjuncts[index]));
}

void SingleInvocationPartition::debugPrint(const char* c)
{
  Trace(c) << "Single invocation variables : ";
  for (unsigned i = 0; i < d_si_vars.size(); i++)
  {
    Trace(c) << d_si_vars[i] << " ";
  }
  Trace(c) << std::endl;
  Trace(c) << "Functions : " << std::endl;
  for (std::map<Node, bool>::iterator it = d_funcs.begin(); it != d_funcs.end();
       ++it)
  {
    Trace(c) << "  " << it->first << " : ";
    if (it->second)
    {
      Trace(c) << d_func_inv[it->first] << " " << d_func_fo_var[it->first]
               << std::endl;
    }
    else
    {
      Trace(c) << "not incorporated." << std::endl;
    }
  }
  for (unsigned i = 0; i < 4; i++)
  {
    Trace(c) << (i == 0 ? "Single invocation"
                        : (i == 1 ? "Non-single invocation"
                                  : (i == 2 ? "All"
                                            : "Non-ground single invocation")));
    Trace(c) << " conjuncts: " << std::endl;
    for (unsigned j = 0; j < d_conjuncts[i].size(); j++)
    {
      Trace(c) << "  " << (j + 1) << " : " << d_conjuncts[i][j] << std::endl;
    }
  }
  Trace(c) << std::endl;
}

} /* namespace CVC4::theory::quantifiers */
} /* namespace CVC4::theory */
} /* namespace CVC4 */
