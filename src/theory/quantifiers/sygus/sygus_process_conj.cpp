/*********************                                                        */
/*! \file sygus_process_conj.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Implementation of techniqures for static preprocessing and analysis
 ** of sygus conjectures.
 **/
#include "theory/quantifiers/sygus/sygus_process_conj.h"

#include <stack>

#include "options/quantifiers_options.h"
#include "theory/quantifiers/sygus/term_database_sygus.h"
#include "theory/quantifiers/term_util.h"

using namespace CVC4::kind;
using namespace std;

namespace CVC4 {
namespace theory {
namespace quantifiers {

void SynthConjectureProcessFun::init(Node f)
{
  d_synth_fun = f;
  Assert(f.getType().isFunction());

  // initialize the arguments
  std::unordered_map<TypeNode, unsigned, TypeNodeHashFunction>
      type_to_init_deq_id;
  std::vector<Type> argTypes =
      static_cast<FunctionType>(f.getType().toType()).getArgTypes();
  for (unsigned j = 0; j < argTypes.size(); j++)
  {
    TypeNode atn = TypeNode::fromType(argTypes[j]);
    std::stringstream ss;
    ss << "a" << j;
    Node k = NodeManager::currentNM()->mkBoundVar(ss.str(), atn);
    d_arg_vars.push_back(k);
    d_arg_var_num[k] = j;
    d_arg_props.push_back(SynthConjectureProcessArg());
  }
}

bool SynthConjectureProcessFun::checkMatch(
    Node cn, Node n, std::unordered_map<unsigned, Node>& n_arg_map)
{
  std::vector<Node> vars;
  std::vector<Node> subs;
  for (std::unordered_map<unsigned, Node>::iterator it = n_arg_map.begin();
       it != n_arg_map.end();
       ++it)
  {
    Assert(it->first < d_arg_vars.size());
    Assert(
        it->second.getType().isComparableTo(d_arg_vars[it->first].getType()));
    vars.push_back(d_arg_vars[it->first]);
    subs.push_back(it->second);
  }
  Node cn_subs =
      cn.substitute(vars.begin(), vars.end(), subs.begin(), subs.end());
  cn_subs = Rewriter::rewrite(cn_subs);
  n = Rewriter::rewrite(n);
  return cn_subs == n;
}

bool SynthConjectureProcessFun::isArgVar(Node n, unsigned& arg_index)
{
  if (n.isVar())
  {
    std::unordered_map<Node, unsigned, NodeHashFunction>::iterator ita =
        d_arg_var_num.find(n);
    if (ita != d_arg_var_num.end())
    {
      arg_index = ita->second;
      return true;
    }
  }
  return false;
}

Node SynthConjectureProcessFun::inferDefinition(
    Node n,
    std::unordered_map<Node, unsigned, NodeHashFunction>& term_to_arg_carry,
    std::unordered_map<Node,
                       std::unordered_set<Node, NodeHashFunction>,
                       NodeHashFunction>& free_vars)
{
  std::unordered_map<TNode, Node, TNodeHashFunction> visited;
  std::unordered_map<TNode, Node, TNodeHashFunction>::iterator it;
  std::stack<TNode> visit;
  TNode cur;
  visit.push(n);
  do
  {
    cur = visit.top();
    visit.pop();
    it = visited.find(cur);
    if (it == visited.end())
    {
      // if it is ground, we can use it
      if (free_vars[cur].empty())
      {
        visited[cur] = cur;
      }
      else
      {
        // if it is term used by another argument, use it
        std::unordered_map<Node, unsigned, NodeHashFunction>::iterator itt =
            term_to_arg_carry.find(cur);
        if (itt != term_to_arg_carry.end())
        {
          visited[cur] = d_arg_vars[itt->second];
        }
        else if (cur.getNumChildren() > 0)
        {
          // try constructing children
          visited[cur] = Node::null();
          visit.push(cur);
          for (unsigned i = 0; i < cur.getNumChildren(); i++)
          {
            visit.push(cur[i]);
          }
        }
        else
        {
          return Node::null();
        }
      }
    }
    else if (it->second.isNull())
    {
      Node ret = cur;
      bool childChanged = false;
      std::vector<Node> children;
      if (cur.getMetaKind() == kind::metakind::PARAMETERIZED)
      {
        children.push_back(cur.getOperator());
      }
      for (unsigned i = 0; i < cur.getNumChildren(); i++)
      {
        it = visited.find(cur[i]);
        Assert(it != visited.end());
        Assert(!it->second.isNull());
        childChanged = childChanged || cur[i] != it->second;
        children.push_back(it->second);
      }
      if (childChanged)
      {
        ret = NodeManager::currentNM()->mkNode(cur.getKind(), children);
      }
      visited[cur] = ret;
    }
  } while (!visit.empty());
  Assert(visited.find(n) != visited.end());
  Assert(!visited.find(n)->second.isNull());
  return visited[n];
}

unsigned SynthConjectureProcessFun::assignRelevantDef(
    Node def, std::vector<unsigned>& args)
{
  unsigned id = 0;
  if (def.isNull())
  {
    // prefer one that already has a definition, if one exists
    for (unsigned j = 0; j < args.size(); j++)
    {
      unsigned i = args[j];
      if (!d_arg_props[i].d_template.isNull())
      {
        id = j;
        break;
      }
    }
  }
  unsigned rid = args[id];
  // for merging previously equivalent definitions
  std::unordered_map<Node, unsigned, NodeHashFunction> prev_defs;
  for (unsigned j = 0; j < args.size(); j++)
  {
    unsigned i = args[j];
    Trace("sygus-process-arg-deps") << "    ...processed arg #" << i;
    if (!d_arg_props[i].d_template.isNull())
    {
      if (d_arg_props[i].d_template == def)
      {
        // definition was consistent
      }
      else
      {
        Node t = d_arg_props[i].d_template;
        std::unordered_map<Node, unsigned, NodeHashFunction>::iterator itt =
            prev_defs.find(t);
        if (itt != prev_defs.end())
        {
          // merge previously equivalent definitions
          d_arg_props[i].d_template = d_arg_vars[itt->second];
          Trace("sygus-process-arg-deps")
              << " (merged equivalent def from argument ";
          Trace("sygus-process-arg-deps") << itt->second << ")." << std::endl;
        }
        else
        {
          // store this as previous
          prev_defs[t] = i;
          // now must be relevant
          d_arg_props[i].d_relevant = true;
          Trace("sygus-process-arg-deps")
              << " (marked relevant, overwrite definition)." << std::endl;
        }
      }
    }
    else
    {
      if (def.isNull())
      {
        if (i != rid)
        {
          // marked as relevant, but template can be set equal to master
          d_arg_props[i].d_template = d_arg_vars[rid];
          Trace("sygus-process-arg-deps") << " (new definition, map to master "
                                          << d_arg_vars[rid] << ")."
                                          << std::endl;
        }
        else
        {
          d_arg_props[i].d_relevant = true;
          Trace("sygus-process-arg-deps") << " (marked relevant)." << std::endl;
        }
      }
      else
      {
        // has new definition
        d_arg_props[i].d_template = def;
        Trace("sygus-process-arg-deps") << " (new definition " << def << ")."
                                        << std::endl;
      }
    }
  }
  return rid;
}

void SynthConjectureProcessFun::processTerms(
    std::vector<Node>& ns,
    std::vector<Node>& ks,
    Node nf,
    std::unordered_set<Node, NodeHashFunction>& synth_fv,
    std::unordered_map<Node,
                       std::unordered_set<Node, NodeHashFunction>,
                       NodeHashFunction>& free_vars)
{
  Assert(ns.size() == ks.size());
  Trace("sygus-process-arg-deps") << "Process " << ns.size()
                                  << " applications of " << d_synth_fun << "..."
                                  << std::endl;

  // get the relevant variables
  // relevant variables are those that appear in the body of the conjunction
  std::unordered_set<Node, NodeHashFunction> rlv_vars;
  Assert(free_vars.find(nf) != free_vars.end());
  rlv_vars = free_vars[nf];

  // get the single occurrence variables
  // single occurrence variables are those that appear in only one position,
  // as an argument to the function-to-synthesize.
  std::unordered_map<Node, bool, NodeHashFunction> single_occ_variables;
  for (unsigned index = 0; index < ns.size(); index++)
  {
    Node n = ns[index];
    for (unsigned i = 0; i < n.getNumChildren(); i++)
    {
      Node nn = n[i];
      if (nn.isVar())
      {
        std::unordered_map<Node, bool, NodeHashFunction>::iterator its =
            single_occ_variables.find(nn);
        if (its == single_occ_variables.end())
        {
          // only irrelevant variables
          single_occ_variables[nn] = rlv_vars.find(nn) == rlv_vars.end();
        }
        else
        {
          single_occ_variables[nn] = false;
        }
      }
      else
      {
        std::unordered_map<Node,
                           std::unordered_set<Node, NodeHashFunction>,
                           NodeHashFunction>::iterator itf = free_vars.find(nn);
        Assert(itf != free_vars.end());
        for (std::unordered_set<Node, NodeHashFunction>::iterator itfv =
                 itf->second.begin();
             itfv != itf->second.end();
             ++itfv)
        {
          single_occ_variables[*itfv] = false;
        }
      }
    }
  }

  // update constant argument information
  for (unsigned index = 0; index < ns.size(); index++)
  {
    Node n = ns[index];
    Trace("sygus-process-arg-deps")
        << "  Analyze argument information for application #" << index << ": "
        << n << std::endl;

    // in the following, we say an argument a "carries" a term t if
    // the function to synthesize would use argument a to construct
    // the term t in its definition.

    // map that assumes all arguments carry their respective term
    std::unordered_map<unsigned, Node> n_arg_map;
    // terms to the argument that is carrying it.
    // the arguments in the range of this map must be marked as relevant.
    std::unordered_map<Node, unsigned, NodeHashFunction> term_to_arg_carry;
    // map of terms to (unprocessed) arguments where it occurs
    std::unordered_map<Node, std::vector<unsigned>, NodeHashFunction>
        term_to_args;

    // initialize
    for (unsigned a = 0; a < n.getNumChildren(); a++)
    {
      n_arg_map[a] = n[a];
    }

    for (unsigned a = 0; a < n.getNumChildren(); a++)
    {
      bool processed = false;
      if (d_arg_props[a].d_relevant)
      {
        // we can assume all relevant arguments carry their terms
        processed = true;
        Trace("sygus-process-arg-deps") << "    ...processed arg #" << a
                                        << " (already relevant)." << std::endl;
        if (term_to_arg_carry.find(n[a]) == term_to_arg_carry.end())
        {
          Trace("sygus-process-arg-deps") << "    carry " << n[a]
                                          << " by argument #" << a << std::endl;
          term_to_arg_carry[n[a]] = a;
        }
      }
      else
      {
        // first, check if single occurrence variable
        // check if an irrelevant variable
        if (n[a].isVar() && synth_fv.find(n[a]) != synth_fv.end())
        {
          Assert(single_occ_variables.find(n[a]) != single_occ_variables.end());
          // may be able to make this more precise?
          // check if a single-occurrence variable
          if (single_occ_variables[n[a]])
          {
            // if we do not already have a template definition, or the
            // template is a single occurrence variable
            if (d_arg_props[a].d_template.isNull()
                || d_arg_props[a].d_var_single_occ)
            {
              processed = true;
              Trace("sygus-process-arg-deps") << "    ...processed arg #" << a;
              Trace("sygus-process-arg-deps")
                  << " (single occurrence variable ";
              Trace("sygus-process-arg-deps") << n[a] << ")." << std::endl;
              d_arg_props[a].d_var_single_occ = true;
              d_arg_props[a].d_template = n[a];
            }
          }
        }
        if (!processed && !d_arg_props[a].d_template.isNull()
            && !d_arg_props[a].d_var_single_occ)
        {
          // argument already has a definition, see if it is maintained
          if (checkMatch(d_arg_props[a].d_template, n[a], n_arg_map))
          {
            processed = true;
            Trace("sygus-process-arg-deps") << "    ...processed arg #" << a;
            Trace("sygus-process-arg-deps") << " (consistent definition "
                                            << n[a];
            Trace("sygus-process-arg-deps")
                << " with " << d_arg_props[a].d_template << ")." << std::endl;
          }
        }
      }
      if (!processed)
      {
        // otherwise, add it to the list of arguments for this term
        term_to_args[n[a]].push_back(a);
      }
    }

    Trace("sygus-process-arg-deps") << "  Look at argument terms..."
                                    << std::endl;

    // list of all arguments
    std::vector<Node> arg_list;
    // now look at the terms for unprocessed arguments
    for (std::unordered_map<Node, std::vector<unsigned>, NodeHashFunction>::
             iterator it = term_to_args.begin();
         it != term_to_args.end();
         ++it)
    {
      Node nn = it->first;
      arg_list.push_back(nn);
      if (Trace.isOn("sygus-process-arg-deps"))
      {
        Trace("sygus-process-arg-deps") << "    argument " << nn;
        Trace("sygus-process-arg-deps") << " (" << it->second.size()
                                        << " positions)";
        // check the status of this term
        if (nn.isVar() && synth_fv.find(nn) != synth_fv.end())
        {
          // is it relevant?
          if (rlv_vars.find(nn) != rlv_vars.end())
          {
            Trace("sygus-process-arg-deps") << " is a relevant variable."
                                            << std::endl;
          }
          else
          {
            Trace("sygus-process-arg-deps") << " is an irrelevant variable."
                                            << std::endl;
          }
        }
        else
        {
          // this can be more precise
          Trace("sygus-process-arg-deps") << " is a relevant term."
                                          << std::endl;
        }
      }
    }

    unsigned arg_list_counter = 0;
    // sort arg_list by term size?

    while (arg_list_counter < arg_list.size())
    {
      Node infer_def_t;
      do
      {
        infer_def_t = Node::null();
        // see if we can infer a definition
        for (std::unordered_map<Node, std::vector<unsigned>, NodeHashFunction>::
                 iterator it = term_to_args.begin();
             it != term_to_args.end();
             ++it)
        {
          Node def = inferDefinition(it->first, term_to_arg_carry, free_vars);
          if (!def.isNull())
          {
            Trace("sygus-process-arg-deps") << "  *** Inferred definition "
                                            << def << " for " << it->first
                                            << std::endl;
            // assign to each argument
            assignRelevantDef(def, it->second);
            // term_to_arg_carry[it->first] = rid;
            infer_def_t = it->first;
            break;
          }
        }
        if (!infer_def_t.isNull())
        {
          term_to_args.erase(infer_def_t);
        }
      } while (!infer_def_t.isNull());

      // decide to make an argument relevant
      bool success = false;
      while (arg_list_counter < arg_list.size() && !success)
      {
        Node curr = arg_list[arg_list_counter];
        std::unordered_map<Node, std::vector<unsigned>, NodeHashFunction>::
            iterator it = term_to_args.find(curr);
        if (it != term_to_args.end())
        {
          Trace("sygus-process-arg-deps") << "  *** Decide relevant " << curr
                                          << std::endl;
          // assign relevant to each
          Node null_def;
          unsigned rid = assignRelevantDef(null_def, it->second);
          term_to_arg_carry[curr] = rid;
          Trace("sygus-process-arg-deps")
              << "    carry " << curr << " by argument #" << rid << std::endl;
          term_to_args.erase(curr);
          success = true;
        }
        arg_list_counter++;
      }
    }
  }
}

bool SynthConjectureProcessFun::isArgRelevant(unsigned i)
{
  return d_arg_props[i].d_relevant;
}

void SynthConjectureProcessFun::getIrrelevantArgs(
    std::unordered_set<unsigned>& args)
{
  for (unsigned i = 0; i < d_arg_vars.size(); i++)
  {
    if (!d_arg_props[i].d_relevant)
    {
      args.insert(i);
    }
  }
}

SynthConjectureProcess::SynthConjectureProcess(QuantifiersEngine* qe) {}
SynthConjectureProcess::~SynthConjectureProcess() {}
Node SynthConjectureProcess::preSimplify(Node q)
{
  Trace("sygus-process") << "Pre-simplify conjecture : " << q << std::endl;
  return q;
}

Node SynthConjectureProcess::postSimplify(Node q)
{
  Trace("sygus-process") << "Post-simplify conjecture : " << q << std::endl;
  Assert(q.getKind() == FORALL);

  if (options::sygusArgRelevant())
  {
    // initialize the information about each function to synthesize
    for (unsigned i = 0, size = q[0].getNumChildren(); i < size; i++)
    {
      Node f = q[0][i];
      if (f.getType().isFunction())
      {
        d_sf_info[f].init(f);
      }
    }

    // get the base on the conjecture
    Node base = q[1];
    std::unordered_set<Node, NodeHashFunction> synth_fv;
    if (base.getKind() == NOT && base[0].getKind() == FORALL)
    {
      for (unsigned j = 0, size = base[0][0].getNumChildren(); j < size; j++)
      {
        synth_fv.insert(base[0][0][j]);
      }
      base = base[0][1];
    }
    std::vector<Node> conjuncts;
    getComponentVector(AND, base, conjuncts);

    // process the conjunctions
    for (std::map<Node, SynthConjectureProcessFun>::iterator it =
             d_sf_info.begin();
         it != d_sf_info.end();
         ++it)
    {
      Node f = it->first;
      for (const Node& conj : conjuncts)
      {
        processConjunct(conj, f, synth_fv);
      }
    }
  }

  return q;
}

void SynthConjectureProcess::initialize(Node n, std::vector<Node>& candidates)
{
  if (Trace.isOn("sygus-process"))
  {
    Trace("sygus-process") << "Process conjecture : " << n
                           << " with candidates: " << std::endl;
    for (unsigned i = 0; i < candidates.size(); i++)
    {
      Trace("sygus-process") << "  " << candidates[i] << std::endl;
    }
  }
}

bool SynthConjectureProcess::isArgRelevant(Node f, unsigned i)
{
  if (!options::sygusArgRelevant())
  {
    return true;
  }
  std::map<Node, SynthConjectureProcessFun>::iterator its = d_sf_info.find(f);
  if (its != d_sf_info.end())
  {
    return its->second.isArgRelevant(i);
  }
  Assert(false);
  return true;
}

bool SynthConjectureProcess::getIrrelevantArgs(
    Node f, std::unordered_set<unsigned>& args)
{
  std::map<Node, SynthConjectureProcessFun>::iterator its = d_sf_info.find(f);
  if (its != d_sf_info.end())
  {
    its->second.getIrrelevantArgs(args);
    return true;
  }
  return false;
}

void SynthConjectureProcess::processConjunct(
    Node n, Node f, std::unordered_set<Node, NodeHashFunction>& synth_fv)
{
  Trace("sygus-process-arg-deps") << "Process conjunct: " << std::endl;
  Trace("sygus-process-arg-deps") << "  " << n << " for synth fun " << f
                                  << "..." << std::endl;

  // first, flatten the conjunct
  // make a copy of free variables since we may add new ones
  std::unordered_set<Node, NodeHashFunction> synth_fv_n = synth_fv;
  std::unordered_map<Node, Node, NodeHashFunction> defs;
  Node nf = flatten(n, f, synth_fv_n, defs);

  Trace("sygus-process-arg-deps") << "Flattened to: " << std::endl;
  Trace("sygus-process-arg-deps") << "  " << nf << std::endl;

  // get free variables in nf
  std::unordered_map<Node,
                     std::unordered_set<Node, NodeHashFunction>,
                     NodeHashFunction>
      free_vars;
  getFreeVariables(nf, synth_fv_n, free_vars);
  // get free variables in each application
  std::vector<Node> ns;
  std::vector<Node> ks;
  for (std::unordered_map<Node, Node, NodeHashFunction>::iterator it =
           defs.begin();
       it != defs.end();
       ++it)
  {
    getFreeVariables(it->second, synth_fv_n, free_vars);
    ns.push_back(it->second);
    ks.push_back(it->first);
  }

  // process the applications of synthesis functions
  if (!ns.empty())
  {
    std::map<Node, SynthConjectureProcessFun>::iterator its = d_sf_info.find(f);
    if (its != d_sf_info.end())
    {
      its->second.processTerms(ns, ks, nf, synth_fv_n, free_vars);
    }
  }
}

Node SynthConjectureProcess::SynthConjectureProcess::flatten(
    Node n,
    Node f,
    std::unordered_set<Node, NodeHashFunction>& synth_fv,
    std::unordered_map<Node, Node, NodeHashFunction>& defs)
{
  std::unordered_map<Node, Node, NodeHashFunction> visited;
  std::unordered_map<Node, Node, NodeHashFunction>::iterator it;
  std::stack<Node> visit;
  Node cur;
  visit.push(n);
  do
  {
    cur = visit.top();
    visit.pop();
    it = visited.find(cur);

    if (it == visited.end())
    {
      visited[cur] = Node::null();
      visit.push(cur);
      for (unsigned i = 0; i < cur.getNumChildren(); i++)
      {
        visit.push(cur[i]);
      }
    }
    else if (it->second.isNull())
    {
      Node ret = cur;
      bool childChanged = false;
      std::vector<Node> children;
      if (cur.getMetaKind() == kind::metakind::PARAMETERIZED)
      {
        children.push_back(cur.getOperator());
      }
      for (unsigned i = 0; i < cur.getNumChildren(); i++)
      {
        it = visited.find(cur[i]);
        Assert(it != visited.end());
        Assert(!it->second.isNull());
        childChanged = childChanged || cur[i] != it->second;
        children.push_back(it->second);
      }
      if (childChanged)
      {
        ret = NodeManager::currentNM()->mkNode(cur.getKind(), children);
      }
      // is it the function to synthesize?
      if (cur.getKind() == APPLY_UF && cur.getOperator() == f)
      {
        // if so, flatten
        Node k = NodeManager::currentNM()->mkBoundVar("vf", cur.getType());
        defs[k] = ret;
        ret = k;
        synth_fv.insert(k);
      }
      // post-rewrite
      visited[cur] = ret;
    }
  } while (!visit.empty());
  Assert(visited.find(n) != visited.end());
  Assert(!visited.find(n)->second.isNull());
  return visited[n];
}

void SynthConjectureProcess::getFreeVariables(
    Node n,
    std::unordered_set<Node, NodeHashFunction>& synth_fv,
    std::unordered_map<Node,
                       std::unordered_set<Node, NodeHashFunction>,
                       NodeHashFunction>& free_vars)
{
  // first must compute free variables in each subterm of n,
  // as well as contains_synth_fun
  std::unordered_map<Node, bool, NodeHashFunction> visited;
  std::unordered_map<Node, bool, NodeHashFunction>::iterator it;
  std::stack<Node> visit;
  Node cur;
  visit.push(n);
  do
  {
    cur = visit.top();
    visit.pop();
    it = visited.find(cur);

    if (it == visited.end())
    {
      visited[cur] = false;
      visit.push(cur);
      for (unsigned i = 0; i < cur.getNumChildren(); i++)
      {
        visit.push(cur[i]);
      }
    }
    else if (!it->second)
    {
      free_vars[cur].clear();
      if (synth_fv.find(cur) != synth_fv.end())
      {
        // it is a free variable
        free_vars[cur].insert(cur);
      }
      else
      {
        // otherwise, carry the free variables from the children
        for (unsigned i = 0; i < cur.getNumChildren(); i++)
        {
          free_vars[cur].insert(free_vars[cur[i]].begin(),
                                free_vars[cur[i]].end());
        }
      }
      visited[cur] = true;
    }
  } while (!visit.empty());
}

Node SynthConjectureProcess::getSymmetryBreakingPredicate(
    Node x, Node e, TypeNode tn, unsigned tindex, unsigned depth)
{
  return Node::null();
}

void SynthConjectureProcess::debugPrint(const char* c) {}
void SynthConjectureProcess::getComponentVector(Kind k,
                                                Node n,
                                                std::vector<Node>& args)
{
  if (n.getKind() == k)
  {
    for (unsigned i = 0; i < n.getNumChildren(); i++)
    {
      args.push_back(n[i]);
    }
  }
  else
  {
    args.push_back(n);
  }
}

} /* namespace CVC4::theory::quantifiers */
} /* namespace CVC4::theory */
} /* namespace CVC4 */
