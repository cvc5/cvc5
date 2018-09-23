/*********************                                                        */
/*! \file enum_stream_concrete.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Haniel Barbosa
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2018 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief class for streaming concrete values from enumerated abstract ones
 **/

#include "theory/quantifiers/sygus/enum_stream_concrete.h"

#include "theory/quantifiers/sygus/term_database_sygus.h"

using namespace CVC4::kind;

namespace CVC4 {
namespace theory {
namespace quantifiers {

StreamPermutation::StreamPermutation(
    Node value,
    const std::vector<std::vector<Node>>& var_classes,
    TermDbSygus* tds)
    : d_tds(tds)
{
  d_value = value;
  for (unsigned i = 0, size = var_classes.size(); i < size; ++i)
  {
    d_perm_state_class.push_back(PermutationState(var_classes[i]));
    d_vars.insert(d_vars.end(), var_classes[i].begin(), var_classes[i].end());
  }
}

Node StreamPermutation::getNextPermutation()
{
  Node perm_value;
  do
  {
    bool new_perm = false;
    std::vector<Node> sub;
    for (unsigned i = 0, size = d_perm_state_class.size(); i < size; ++i)
    {
      std::vector<Node> perm;
      if (!d_perm_state_class[i].getNextPermutation(perm))
      {
        d_perm_state_class[i].getLastPermutation(perm);
      }
      else
      {
        new_perm = true;
      }
      sub.insert(sub.end(), perm.begin(), perm.end());
    }
    // no new permutation
    if (!new_perm)
    {
      return Node::null();
    }
    perm_value = d_value.substitute(
        d_vars.begin(), d_vars.end(), sub.begin(), sub.end());
    perm_value = d_tds->getExtRewriter()->extendedRewrite(perm_value);
    // if permuted value is equivalent modulo rewriting to a previous one, look
    // for another
  } while (!d_perm_values.insert(perm_value).second);
  return perm_value;
}

StreamPermutation::PermutationState::PermutationState(
    const std::vector<Node>& vars)
{
  d_vars = vars;
  std::fill(d_seq.begin(), d_seq.end(), 0);
  d_curr_ind = 0;
}

void StreamPermutation::PermutationState::getLastPermutation(
    std::vector<Node>& perm)
{
  perm.insert(perm.end(), d_last_perm.begin(), d_last_perm.end());
}

bool StreamPermutation::PermutationState::getNextPermutation(
    std::vector<Node>& perm)
{
  // initial case
  if (d_last_perm.empty())
  {
    d_last_perm = d_vars;
    perm = d_vars;
    return true;
  }
  // exhausted permutations
  if (d_curr_ind == d_vars.size())
  {
    return false;
  }
  if (d_seq[d_curr_ind] >= d_curr_ind)
  {
    d_seq[d_curr_ind++] = 0;
    return getNextPermutation(perm);
  }
  perm = d_last_perm;
  if (d_curr_ind % 2 == 0)
  {
    // swap with first element
    std::swap(perm[0], perm[d_curr_ind]);
  }
  else
  {
    // swap with element in index in sequence of current index
    std::swap(perm[d_seq[d_curr_ind]], perm[d_curr_ind]);
  }
  d_seq[d_curr_ind] += 1;
  d_curr_ind = 0;
  return true;
}

EnumStreamConcrete::EnumStreamConcrete(QuantifiersEngine* qe,
                                       SynthConjecture* p)
    : d_qe(qe), d_tds(qe->getTermDatabaseSygus()), d_parent(p)
{
}

void EnumStreamConcrete::collectVars(
    Node n,
    std::vector<Node>& vars,
    std::unordered_set<Node, NodeHashFunction>& visited)
{
  if (visited.find(n) != visited.end())
  {
    return;
  }
  visited.insert(n);
  if (n.getKind() == kind::BOUND_VARIABLE)
  {
    if (std::find(vars.begin(), vars.end(), n) == vars.end())
    {
      vars.push_back(n);
    }
    return;
  }
  for (const Node& ni : n)
  {
    collectVars(ni, vars, visited);
  }
}

void EnumStreamConcrete::splitVarClasses(
    const std::vector<Node>& vars, std::vector<std::vector<Node>>& var_classes)
{
  std::unordered_set<unsigned> seen_classes;
  for (unsigned i = 0, size = vars.size(); i < size - 1; ++i)
  {
    unsigned curr_class = d_var_class[vars[i]];
    if (!seen_classes.insert(curr_class).second)
    {
      continue;
    }
    var_classes.push_back(std::vector<Node>());
    for (unsigned j = i; j < size; ++j)
    {
      if (d_var_class[vars[j]] == curr_class)
      {
        var_classes.back().push_back(vars[j]);
      }
    }
  }
}

void EnumStreamConcrete::registerEnumerator(Node e)
{
  // get variables in enumerator
  TypeNode tn = e.getType();
  const Datatype& dt = tn.getDatatype();
  Node var_list = Node::fromExpr(dt.getSygusVarList());
  for (const Node& v : var_list)
  {
    d_var_class[v] = d_tds->getSubclassForVar(tn, v);
    Assert(d_var_class[v] > 0);
  }
}

void EnumStreamConcrete::registerAbstractValue(Node v)
{
  d_abs_values.push_back(v);
  std::vector<Node> vars;
  std::unordered_set<Node, NodeHashFunction> visited;
  collectVars(v, vars, visited);
  std::vector<std::vector<Node>> var_classes;
  if (!vars.empty())
  {
    splitVarClasses(vars, var_classes);
  }
  d_stream_permutations.push_back(StreamPermutation(v, var_classes, d_tds));
}

Node EnumStreamConcrete::getNext()
{
  Assert(!d_stream_permutations.empty());
  return d_stream_permutations.back().getNextPermutation();
}

}  // namespace quantifiers
}  // namespace theory
}  // namespace CVC4
