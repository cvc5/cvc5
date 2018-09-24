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

#include "options/base_options.h"
#include "options/quantifiers_options.h"
#include "printer/printer.h"
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
  std::stringstream ss;
  Printer::getPrinter(options::outputLanguage())->toStreamSygus(ss, d_value);
  Trace("synth-stream-concrete")
      << " ..streaming next permutation for value : " << ss.str() << " with "
      << d_perm_state_class.size() << " permutation classes\n";
  Node perm_value, bultin_perm_value;
  do
  {
    bool new_perm = false;
    std::vector<Node> sub;
    for (unsigned i = 0, size = d_perm_state_class.size(); i < size; ++i)
    {
      Trace("synth-stream-concrete-debug2") << " ....class " << i << " : ";
      if (d_perm_state_class[i].getNextPermutation())
      {
        new_perm = true;
        Trace("synth-stream-concrete-debug2") << "new perm\n";
      }
      else
      {
        Trace("synth-stream-concrete-debug2") << "last perm\n";
      }
      sub.insert(sub.end(),
                 d_perm_state_class[i].d_last_perm.begin(),
                 d_perm_state_class[i].d_last_perm.end());
      if (Trace.isOn("synth-stream-concrete-debug2"))
      {
        Trace("synth-stream-concrete-debug2") << "  ....sub is :";
        for (unsigned j = 0, size_j = d_perm_state_class[i].d_last_perm.size();
             j < size_j;
             ++j)
        {
          ss.str("");
          Printer::getPrinter(options::outputLanguage())
              ->toStreamSygus(ss, d_perm_state_class[i].d_vars[j]);
          Trace("synth-stream-concrete-debug2") << " " << ss.str();
          ss.str("");
          Printer::getPrinter(options::outputLanguage())
              ->toStreamSygus(ss, d_perm_state_class[i].d_last_perm[j]);
          Trace("synth-stream-concrete-debug2") << " -> " << ss.str() << "; ";
        }
        Trace("synth-stream-concrete-debug2") << "\n";
      }
    }
    // no new permutation
    if (!new_perm)
    {
      Trace("synth-stream-concrete") << " ..no new perm, return null\n";
      return Node::null();
    }
    perm_value = d_value.substitute(
        d_vars.begin(), d_vars.end(), sub.begin(), sub.end());
    bultin_perm_value = d_tds->sygusToBuiltin(perm_value, perm_value.getType());
    Trace("synth-stream-concrete-debug")
        << " ....perm is " << bultin_perm_value;

    bultin_perm_value =
        d_tds->getExtRewriter()->extendedRewrite(bultin_perm_value);

    Trace("synth-stream-concrete-debug")
        << " and rewrites to " << bultin_perm_value << "\n";
    // if permuted value is equivalent modulo rewriting to a previous one, look
    // for another
  } while (!d_perm_values.insert(bultin_perm_value).second);

  Trace("synth-stream-concrete")
      << " ..return new perm " << bultin_perm_value << "\n";
  return perm_value;
}

StreamPermutation::PermutationState::PermutationState(
    const std::vector<Node>& vars)
{
  d_vars = vars;
  d_seq.resize(vars.size());
  std::fill(d_seq.begin(), d_seq.end(), 0);
  d_curr_ind = 0;
}

bool StreamPermutation::PermutationState::getNextPermutation()
{
  // initial case
  if (d_last_perm.empty())
  {
    Trace("synth-stream-concrete-debug2") << "initial perm, ";
    d_last_perm = d_vars;
    return true;
  }
  // exhausted permutations
  if (d_curr_ind == d_vars.size())
  {
    Trace("synth-stream-concrete-debug2") << "exhausted perms, ";
    return false;
  }
  if (d_seq[d_curr_ind] >= d_curr_ind)
  {
    d_seq[d_curr_ind] = 0;
    d_curr_ind++;
    return getNextPermutation();
  }
  if (d_curr_ind % 2 == 0)
  {
    // swap with first element
    std::swap(d_last_perm[0], d_last_perm[d_curr_ind]);
  }
  else
  {
    // swap with element in index in sequence of current index
    std::swap(d_last_perm[d_seq[d_curr_ind]], d_last_perm[d_curr_ind]);
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
  if (n.getNumChildren() > 0)
  {
    for (const Node& ni : n)
    {
      collectVars(ni, vars, visited);
    }
    return;
  }
  if (d_tds->sygusToBuiltin(n, n.getType()).getKind() == kind::BOUND_VARIABLE)
  {
    if (std::find(vars.begin(), vars.end(), n) == vars.end())
    {
      vars.push_back(n);
    }
    return;
  }
}

void EnumStreamConcrete::splitVarClasses(
    const std::vector<Node>& vars, std::vector<std::vector<Node>>& var_classes)
{
  if (vars.size() == 1)
  {
    var_classes.push_back(std::vector<Node>());
    var_classes.back().push_back(vars[0]);
    return;
  }
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
  Trace("synth-stream-concrete")
      << " * Streaming concrete: registering enum " << e;
  d_enum = e;
  // get variables in enumerator
  TypeNode tn = e.getType();
  const Datatype& dt = tn.getDatatype();
  Node var_list = Node::fromExpr(dt.getSygusVarList());
  Trace("synth-stream-concrete") << " with variables :";
  for (const Node& v : var_list)
  {
    d_var_class[v] = d_tds->getSubclassForVar(tn, v);
    Assert(d_var_class[v] > 0);
    std::stringstream ss;
    Printer::getPrinter(options::outputLanguage())->toStreamSygus(ss, v);
    Trace("synth-stream-concrete")
        << " " << ss.str() << "[" << d_var_class[v] << "]";
  }
  Trace("synth-stream-concrete") << "\n";
}

void EnumStreamConcrete::registerAbstractValue(Node v)
{
  d_abs_values.push_back(v);
  std::stringstream ss;
  Printer::getPrinter(options::outputLanguage())->toStreamSygus(ss, v);
  Trace("synth-stream-concrete")
      << " * Streaming concrete: registering for enum " << d_enum << " value "
      << ss.str();
  std::vector<Node> vars;
  std::unordered_set<Node, NodeHashFunction> visited;
  collectVars(v, vars, visited);
  std::vector<std::vector<Node>> var_classes;
  if (!vars.empty())
  {
    splitVarClasses(vars, var_classes);
    if (Trace.isOn("synth-stream-concrete"))
    {
      Trace("synth-stream-concrete") << " with vars ";
      for (auto& var : vars)
      {
        ss.str("");
        Printer::getPrinter(options::outputLanguage())->toStreamSygus(ss, var);
        Trace("synth-stream-concrete") << " " << ss.str();
      }
      Trace("synth-stream-concrete") << "\n  ..var classes : ";
      for (auto& v_class : var_classes)
      {
        Trace("synth-stream-concrete") << " [";
        for (auto& var : v_class)
        {
          ss.str("");
          Printer::getPrinter(options::outputLanguage())
              ->toStreamSygus(ss, var);
          Trace("synth-stream-concrete") << " " << ss.str();
        }
        Trace("synth-stream-concrete") << " ]";
      }
      Trace("synth-stream-concrete") << "\n";
    }
  }
  else
  {
    Trace("synth-stream-concrete") << " with no vars\n";
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
