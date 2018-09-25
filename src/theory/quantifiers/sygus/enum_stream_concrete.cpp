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

#include <numeric>  // for std::iota

using namespace CVC4::kind;

namespace CVC4 {
namespace theory {
namespace quantifiers {

StreamPermutation::StreamPermutation(
    Node value,
    const std::vector<Node>& perm_vars,
    const std::vector<std::vector<Node>>& var_classes,
    TermDbSygus* tds)
    : d_tds(tds)
{
  d_curr_ind = 0;
  d_value = value;
  d_vars = perm_vars;
  for (unsigned i = 0, size = var_classes.size(); i < size; ++i)
  {
    d_perm_state_class.push_back(PermutationState(var_classes[i]));
  }
  // initial value
  d_last_value = value;
  Node bultin_value = d_tds->sygusToBuiltin(value, value.getType());
  d_perm_values.insert(d_tds->getExtRewriter()->extendedRewrite(bultin_value));
}

Node StreamPermutation::getNext()
{
  if (Trace.isOn("synth-stream-concrete"))
  {
    std::stringstream ss;
    Printer::getPrinter(options::outputLanguage())->toStreamSygus(ss, d_value);
    Trace("synth-stream-concrete")
        << " ....streaming next permutation for value : " << ss.str()
        << " with " << d_perm_state_class.size() << " permutation classes\n";
  }
  unsigned n_classes = d_perm_state_class.size();
  Assert(n_classes > 0);
  Node perm_value, bultin_perm_value;
  do
  {
    bool new_perm = false;
    do
    {
      if (d_perm_state_class[d_curr_ind].getNextPermutation())
      {
        new_perm = true;
        Trace("synth-stream-concrete-debug2")
            << " ....class " << d_curr_ind << " has new perm\n";
        d_curr_ind = 0;
      }
      else
      {
        Trace("synth-stream-concrete-debug2")
            << " ....class " << d_curr_ind << " reset\n";
        d_perm_state_class[d_curr_ind].reset();
        d_curr_ind++;
      }
    } while (!new_perm && d_curr_ind < n_classes);
    // no new permutation
    if (!new_perm)
    {
      Trace("synth-stream-concrete") << " ....no new perm, return null\n";
      return Node::null();
    }
    // build sub
    std::vector<Node> sub;
    for (unsigned i = 0, size = d_perm_state_class.size(); i < size; ++i)
    {
      sub.insert(sub.end(),
                 d_perm_state_class[i].d_last_perm.begin(),
                 d_perm_state_class[i].d_last_perm.end());
    }
    if (Trace.isOn("synth-stream-concrete-debug2"))
    {
      Trace("synth-stream-concrete-debug2") << "  ......sub is :";
      for (unsigned i = 0, size = d_vars.size(); i < size; ++i)
      {
        std::stringstream ss;
        Printer::getPrinter(options::outputLanguage())
            ->toStreamSygus(ss, d_vars[i]);
        Trace("synth-stream-concrete-debug2") << " " << ss.str();
        ss.str("");
        Printer::getPrinter(options::outputLanguage())
            ->toStreamSygus(ss, sub[i]);
        Trace("synth-stream-concrete-debug2") << " -> " << ss.str() << "; ";
      }
      Trace("synth-stream-concrete-debug2") << "\n";
    }
    perm_value = d_value.substitute(
        d_vars.begin(), d_vars.end(), sub.begin(), sub.end());
    bultin_perm_value = d_tds->sygusToBuiltin(perm_value, perm_value.getType());
    Trace("synth-stream-concrete-debug")
        << " ......perm is " << bultin_perm_value;

    bultin_perm_value =
        d_tds->getExtRewriter()->extendedRewrite(bultin_perm_value);

    Trace("synth-stream-concrete-debug")
        << " and rewrites to " << bultin_perm_value << "\n";
    // if permuted value is equivalent modulo rewriting to a previous one, look
    // for another
  } while (!d_perm_values.insert(bultin_perm_value).second);
  if (Trace.isOn("synth-stream-concrete"))
  {
    std::stringstream ss;
    Printer::getPrinter(options::outputLanguage())
        ->toStreamSygus(ss, perm_value);
    Trace("synth-stream-concrete")
        << " ....return new perm " << ss.str() << "\n";
  }
  d_last_value = perm_value;
  return perm_value;
}

Node StreamPermutation::getLast() { return d_last_value; }

StreamPermutation::PermutationState::PermutationState(
    const std::vector<Node>& vars)
{
  d_vars = vars;
  d_seq.resize(vars.size());
  std::fill(d_seq.begin(), d_seq.end(), 0);
  d_curr_ind = 0;
  d_last_perm = d_vars;
}

void StreamPermutation::PermutationState::reset()
{
  d_seq.clear();
  d_seq.resize(d_vars.size());
  std::fill(d_seq.begin(), d_seq.end(), 0);
  d_curr_ind = 0;
  d_last_perm = d_vars;
}

bool StreamPermutation::PermutationState::getNextPermutation()
{
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

StreamCombination::StreamCombination(
    Node value,
    const std::map<Node, std::vector<Node>>& var_cons,
    const std::vector<Node>& all_vars,
    const std::vector<std::vector<Node>>& all_var_classes,
    const std::vector<Node>& perm_vars,
    const std::vector<std::vector<Node>>& perm_var_classes,
    TermDbSygus* tds)
    : d_tds(tds), d_stream_permutations(value, perm_vars, perm_var_classes, tds)
{
  Assert(all_vars.size() >= perm_vars.size());
  d_curr_ind = 0;
  d_all_vars = all_vars;
  d_perm_vars = perm_vars;
  d_var_cons = var_cons;
  for (unsigned i = 0, size = all_var_classes.size(); i < size; ++i)
  {
    d_comb_state_class.push_back(CombinationState(
        all_var_classes[i].size(),
        i < perm_var_classes.size() ? perm_var_classes[i].size() : 0,
        all_var_classes[i]));
  }
}

Node StreamCombination::getNext()
{
  Trace("synth-stream-concrete")
      << " ..streaming next combination of " << d_perm_vars.size() << " vars\n";
  unsigned n_classes = d_comb_state_class.size();
  // if no variables
  if (d_perm_vars.size() == 0)
  {
    if (d_last.isNull())
    {
      if (Trace.isOn("synth-stream-concrete"))
      {
        std::stringstream ss;
        Printer::getPrinter(options::outputLanguage())
            ->toStreamSygus(ss, d_stream_permutations.getLast());
        Trace("synth-stream-concrete")
            << " ..only comb is " << ss.str() << "\n";
      }
      d_last = d_stream_permutations.getLast();
      return d_last;
    }
    else
    {
      Trace("synth-stream-concrete") << " ..no new comb, return null\n";
      return Node::null();
    }
  }
  // if not in intial case
  if (!d_last.isNull())
  {
    bool new_comb = false;
    do
    {
      if (d_comb_state_class[d_curr_ind].getNextCombination())
      {
        new_comb = true;
        Trace("synth-stream-concrete-debug2")
            << " ....class " << d_curr_ind << " has new comb\n";
        d_curr_ind = 0;
      }
      else
      {
        Trace("synth-stream-concrete-debug2")
            << " ....class " << d_curr_ind << " reset\n";
        d_comb_state_class[d_curr_ind].reset();
        d_curr_ind++;
      }
    } while (!new_comb && d_curr_ind < n_classes);
    // no new combination
    if (!new_comb)
    {
      Trace("synth-stream-concrete")
          << " ..no new comb, get next permutation\n";
#ifdef CVC4_ASSERTIONS
      Trace("synth-stream-concrete")
          << " ....total combs until here : " << d_comb_values.size() << "\n";
#endif
      d_last = d_stream_permutations.getNext();
      // exhausted permutations
      if (d_last.isNull())
      {
        Trace("synth-stream-concrete") << " ..no new comb, return null\n";
        return Node::null();
      }
      // reset combination classes for next permutation
      d_curr_ind = 0;
      for (unsigned i = 0, size = d_comb_state_class.size(); i < size; ++i)
      {
        d_comb_state_class[i].reset();
      }
    }
  }
  else
  {
    d_last = d_stream_permutations.getLast();
  }
  // building substitution
  std::vector<Node> sub;
  for (unsigned i = 0, size = d_comb_state_class.size(); i < size; ++i)
  {
    Trace("synth-stream-concrete") << " ..comb for class " << i << " is";
    std::vector<Node> raw_sub;
    d_comb_state_class[i].getLastVars(raw_sub);
    unsigned curr_size = sub.size();
    // build proper substitution based on variables types and constructors
    for (unsigned j = 0, size_j = raw_sub.size(); j < size_j; ++j)
    {
      TypeNode perm_var_tn = d_perm_vars[j + curr_size].getType();
      Assert(!d_var_cons[raw_sub[j]].empty());
      for (const Node& cons : d_var_cons[raw_sub[j]])
      {
        if (cons.getType() == perm_var_tn)
        {
          Trace("synth-stream-concrete-debug2")
              << "\n ....{ replacing " << raw_sub[j] << " ["
              << raw_sub[j].getType() << "] by " << cons << " ["
              << cons.getType() << "] }";
          raw_sub[j] = cons;
          break;
        }
      }
    }
    sub.insert(sub.end(), raw_sub.begin(), raw_sub.end());
    Trace("synth-stream-concrete") << "\n";
  }
  // build substitution with last combination
  Assert(d_perm_vars.size() == sub.size());
  if (Trace.isOn("synth-stream-concrete-debug2"))
  {
    std::stringstream ss;
    Printer::getPrinter(options::outputLanguage())->toStreamSygus(ss, d_last);
    Trace("synth-stream-concrete-debug2")
        << "  ....sub on " << ss.str() << " is :";
    for (unsigned j = 0, size_j = d_perm_vars.size(); j < size_j; ++j)
    {
      std::stringstream ss1, ss2;
      Printer::getPrinter(options::outputLanguage())
          ->toStreamSygus(ss1, d_perm_vars[j]);
      Printer::getPrinter(options::outputLanguage())
          ->toStreamSygus(ss2, sub[j]);
      Trace("synth-stream-concrete-debug2")
          << " " << ss1.str() << " [ " << d_perm_vars[j].getType() << " ] -> "
          << ss2.str() << " [ " << sub[j].getType() << " ]"
          << "; ";
      Assert(d_perm_vars[j].getType() == sub[j].getType());
    }
    Trace("synth-stream-concrete-debug2") << "\n";
  }
  Node comb_value = d_last.substitute(
      d_perm_vars.begin(), d_perm_vars.end(), sub.begin(), sub.end());
  if (Trace.isOn("synth-stream-concrete"))
  {
    std::stringstream ss;
    Printer::getPrinter(options::outputLanguage())
        ->toStreamSygus(ss, comb_value);
    Trace("synth-stream-concrete")
        << " ..return new comb " << ss.str() << "\n\n";
  }
#ifdef CVC4_ASSERTIONS
  // the new combination value should be fresh, modulo rewriting, by
  // construction (unless it's equiv to a constant, e.g. true / false)
  Node builtin_comb_value = d_tds->getExtRewriter()->extendedRewrite(
      d_tds->sygusToBuiltin(comb_value, comb_value.getType()));
  Assert(builtin_comb_value.isConst()
         || d_comb_values.insert(builtin_comb_value).second);
#endif
  return comb_value;
}

StreamCombination::CombinationState::CombinationState(
    unsigned n, unsigned k, const std::vector<Node>& vars)
    : d_n(n), d_k(k)
{
  Assert(k <= n);
  d_last_comb.resize(k);
  std::iota(d_last_comb.begin(), d_last_comb.end(), 0);
  d_vars_class = vars;
}

void StreamCombination::CombinationState::reset()
{
  std::iota(d_last_comb.begin(), d_last_comb.end(), 0);
}

void StreamCombination::CombinationState::getLastVars(std::vector<Node>& vars)
{
  for (unsigned i = 0, size = d_last_comb.size(); i < size; ++i)
  {
    std::stringstream ss;
    Printer::getPrinter(options::outputLanguage())
        ->toStreamSygus(ss, d_vars_class[d_last_comb[i]]);
    Trace("synth-stream-concrete") << " " << ss.str();
    vars.push_back(d_vars_class[d_last_comb[i]]);
  }
}

bool StreamCombination::CombinationState::getNextCombination()
{
  // find what to increment
  bool new_comb = false;
  for (int i = d_k - 1; i >= 0; --i)
  {
    if (d_last_comb[i] < d_n - d_k + i)
    {
      unsigned j = d_last_comb[i] + 1;
      while (static_cast<unsigned>(i) <= d_k - 1)
      {
        d_last_comb[i++] = j++;
      }
      new_comb = true;
      break;
    }
  }
  return new_comb;
}

EnumStreamConcrete::EnumStreamConcrete(QuantifiersEngine* qe,
                                       SynthConjecture* p)
    : d_qe(qe), d_parent(p), d_tds(qe->getTermDatabaseSygus())
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
  Node var_list = Node::fromExpr(tn.getDatatype().getSygusVarList());
  // get subtypes in enumerator's type
  NodeManager* nm = NodeManager::currentNM();
  std::vector<TypeNode> sf_types;
  d_tds->getSubfieldTypes(tn, sf_types);
  Trace("synth-stream-concrete") << " with variables :";
  for (const Node& v : var_list)
  {
    if (Trace.isOn("synth-stream-concrete"))
    {
      std::stringstream ss;
      Printer::getPrinter(options::outputLanguage())->toStreamSygus(ss, v);
      Trace("synth-stream-concrete")
          << " " << ss.str() << "[" << d_var_class[v];
    }
    d_vars.push_back(v);
    d_var_class[v] = d_tds->getSubclassForVar(tn, v);
    Assert(d_var_class[v] > 0);
    // collect constructors for variable in all subtypes
    std::vector<Node> cons;
    for (const TypeNode& stn : sf_types)
    {
      const Datatype& dt = stn.getDatatype();
      for (unsigned i = 0, size = dt.getNumConstructors(); i < size; ++i)
      {
        if (dt[i].getNumArgs() == 0 && Node::fromExpr(dt[i].getSygusOp()) == v)
        {
          cons.push_back(nm->mkNode(APPLY_CONSTRUCTOR, dt[i].getConstructor()));
        }
      }
    }
    d_var_cons[v] = cons;
    Trace("synth-stream-concrete") << "; " << cons.size() << "]";
  }
  Trace("synth-stream-concrete") << "\n";
  // split enum vars into classes
  splitVarClasses(d_vars, d_var_classes);
}

void EnumStreamConcrete::registerAbstractValue(Node v)
{
  d_abs_values.push_back(v);
  if (Trace.isOn("synth-stream-concrete"))
  {
    std::stringstream ss;
    Printer::getPrinter(options::outputLanguage())->toStreamSygus(ss, v);
    Trace("synth-stream-concrete")
        << " * Streaming concrete: registering for enum " << d_enum << " value "
        << ss.str();
  }
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
      for (const Node& var : vars)
      {
        std::stringstream ss;
        Printer::getPrinter(options::outputLanguage())->toStreamSygus(ss, var);
        Trace("synth-stream-concrete") << " " << ss.str();
      }
      Trace("synth-stream-concrete") << "\n  ..var classes : ";
      for (auto& v_class : var_classes)
      {
        Trace("synth-stream-concrete") << " [";
        for (const Node& var : v_class)
        {
          std::stringstream ss;
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
  d_stream_combinations.push_back(StreamCombination(
      v, d_var_cons, d_vars, d_var_classes, vars, var_classes, d_tds));
}

Node EnumStreamConcrete::getNext()
{
  Assert(!d_stream_combinations.empty());
  return d_stream_combinations.back().getNext();
}

}  // namespace quantifiers
}  // namespace theory
}  // namespace CVC4
