/*********************                                                        */
/*! \file enum_stream_substitution.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Haniel Barbosa, Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief class for streaming concrete values (through substitutions) from
 ** enumerated abstract ones
 **/

#include "theory/quantifiers/sygus/enum_stream_substitution.h"

#include "options/base_options.h"
#include "options/datatypes_options.h"
#include "options/quantifiers_options.h"
#include "printer/printer.h"
#include "theory/quantifiers/sygus/term_database_sygus.h"

#include <numeric>  // for std::iota

using namespace CVC4::kind;

namespace CVC4 {
namespace theory {
namespace quantifiers {

EnumStreamPermutation::EnumStreamPermutation(quantifiers::TermDbSygus* tds)
    : d_tds(tds), d_first(true), d_curr_ind(0)
{
}

void EnumStreamPermutation::reset(Node value)
{
  // clean state
  d_var_classes.clear();
  d_var_tn_cons.clear();
  d_first = true;
  d_perm_state_class.clear();
  d_perm_values.clear();
  d_value = value;
  // get variables in value's type
  TypeNode tn = value.getType();
  Node var_list = tn.getDType().getSygusVarList();
  NodeManager* nm = NodeManager::currentNM();
  // get subtypes in value's type
  SygusTypeInfo& ti = d_tds->getTypeInfo(tn);
  std::vector<TypeNode> sf_types;
  ti.getSubfieldTypes(sf_types);
  // associate variables with constructors in all subfield types
  std::map<Node, Node> cons_var;
  for (const Node& v : var_list)
  {
    // collect constructors for variable in all subtypes
    for (const TypeNode& stn : sf_types)
    {
      const DType& dt = stn.getDType();
      for (unsigned i = 0, size = dt.getNumConstructors(); i < size; ++i)
      {
        if (dt[i].getNumArgs() == 0 && dt[i].getSygusOp() == v)
        {
          Node cons = nm->mkNode(APPLY_CONSTRUCTOR, dt[i].getConstructor());
          d_var_tn_cons[v][stn] = cons;
          cons_var[cons] = v;
        }
      }
    }
  }
  // collect variables occurring in value
  std::vector<Node> vars;
  std::unordered_set<Node, NodeHashFunction> visited;
  collectVars(value, vars, visited);
  // partition permutation variables
  d_curr_ind = 0;
  Trace("synth-stream-concrete") << " ..permutting vars :";
  std::unordered_set<Node, NodeHashFunction> seen_vars;
  for (const Node& v_cons : vars)
  {
    Assert(cons_var.find(v_cons) != cons_var.end());
    Node var = cons_var[v_cons];
    if (seen_vars.insert(var).second)
    {
      // do not add repeated vars
      d_var_classes[ti.getSubclassForVar(var)].push_back(var);
    }
  }
  for (const std::pair<unsigned, std::vector<Node>>& p : d_var_classes)
  {
    d_perm_state_class.push_back(PermutationState(p.second));
    if (Trace.isOn("synth-stream-concrete"))
    {
      Trace("synth-stream-concrete") << " " << p.first << " -> [";
      for (const Node& var : p.second)
      {
        std::stringstream ss;
        Printer::getPrinter(options::outputLanguage())->toStreamSygus(ss, var);
        Trace("synth-stream-concrete") << " " << ss.str();
      }
      Trace("synth-stream-concrete") << " ]";
    }
  }
  Trace("synth-stream-concrete") << "\n";
}

Node EnumStreamPermutation::getNext()
{
  if (Trace.isOn("synth-stream-concrete"))
  {
    std::stringstream ss;
    Printer::getPrinter(options::outputLanguage())->toStreamSygus(ss, d_value);
    Trace("synth-stream-concrete")
        << " ....streaming next permutation for value : " << ss.str()
        << " with " << d_perm_state_class.size() << " permutation classes\n";
  }
  // initial value
  if (d_first)
  {
    d_first = false;
    Node bultin_value = d_tds->sygusToBuiltin(d_value, d_value.getType());
    d_perm_values.insert(
        d_tds->getExtRewriter()->extendedRewrite(bultin_value));
    return d_value;
  }
  unsigned n_classes = d_perm_state_class.size();
  Node perm_value, bultin_perm_value;
  do
  {
    bool new_perm = false;
    while (!new_perm && d_curr_ind < n_classes)
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
    }
    // no new permutation
    if (!new_perm)
    {
      Trace("synth-stream-concrete") << " ....no new perm, return null\n";
      return Node::null();
    }
    // building substitution
    std::vector<Node> domain_sub, range_sub;
    for (unsigned i = 0, size = d_perm_state_class.size(); i < size; ++i)
    {
      Trace("synth-stream-concrete") << " ..perm for class " << i << " is";
      std::vector<Node> raw_sub;
      d_perm_state_class[i].getLastPerm(raw_sub);
      // retrieve variables for substitution domain
      const std::vector<Node>& domain_sub_class =
          d_perm_state_class[i].getVars();
      Assert(domain_sub_class.size() == raw_sub.size());
      // build proper substitution based on variables types and constructors
      for (unsigned j = 0, size_j = raw_sub.size(); j < size_j; ++j)
      {
        for (std::pair<const TypeNode, Node>& p :
             d_var_tn_cons[domain_sub_class[j]])
        {
          // get constructor of type p.first from variable being permuted
          domain_sub.push_back(p.second);
          // get constructor of type p.first from variable to be permuted for
          range_sub.push_back(d_var_tn_cons[raw_sub[j]][p.first]);
          Trace("synth-stream-concrete-debug2")
              << "\n ....{ adding " << domain_sub.back() << " ["
              << domain_sub.back().getType() << "] -> " << range_sub.back()
              << " [" << range_sub.back().getType() << "] }";
        }
      }
      Trace("synth-stream-concrete") << "\n";
    }
    perm_value = d_value.substitute(domain_sub.begin(),
                                    domain_sub.end(),
                                    range_sub.begin(),
                                    range_sub.end());
    bultin_perm_value = d_tds->sygusToBuiltin(perm_value, perm_value.getType());
    Trace("synth-stream-concrete-debug")
        << " ......perm builtin is " << bultin_perm_value;
    if (options::sygusSymBreakDynamic())
    {
      bultin_perm_value =
          d_tds->getExtRewriter()->extendedRewrite(bultin_perm_value);
      Trace("synth-stream-concrete-debug")
          << " and rewrites to " << bultin_perm_value;
    }
    Trace("synth-stream-concrete-debug") << "\n";
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
  return perm_value;
}

const std::vector<Node>& EnumStreamPermutation::getVarsClass(unsigned id) const
{
  std::map<unsigned, std::vector<Node>>::const_iterator it =
      d_var_classes.find(id);
  Assert(it != d_var_classes.end());
  return it->second;
}

unsigned EnumStreamPermutation::getVarClassSize(unsigned id) const
{
  std::map<unsigned, std::vector<Node>>::const_iterator it =
      d_var_classes.find(id);
  if (it == d_var_classes.end())
  {
    return 0;
  }
  return it->second.size();
}

void EnumStreamPermutation::collectVars(
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

EnumStreamPermutation::PermutationState::PermutationState(
    const std::vector<Node>& vars)
{
  d_vars = vars;
  d_curr_ind = 0;
  d_seq.resize(vars.size());
  std::fill(d_seq.begin(), d_seq.end(), 0);
  // initialize variable indices
  d_last_perm.resize(vars.size());
  std::iota(d_last_perm.begin(), d_last_perm.end(), 0);
}

void EnumStreamPermutation::PermutationState::reset()
{
  d_curr_ind = 0;
  std::fill(d_seq.begin(), d_seq.end(), 0);
  std::iota(d_last_perm.begin(), d_last_perm.end(), 0);
}

const std::vector<Node>& EnumStreamPermutation::PermutationState::getVars()
    const
{
  return d_vars;
}

void EnumStreamPermutation::PermutationState::getLastPerm(
    std::vector<Node>& vars)
{
  for (unsigned i = 0, size = d_last_perm.size(); i < size; ++i)
  {
    if (Trace.isOn("synth-stream-concrete"))
    {
      std::stringstream ss;
      Printer::getPrinter(options::outputLanguage())
          ->toStreamSygus(ss, d_vars[d_last_perm[i]]);
      Trace("synth-stream-concrete") << " " << ss.str();
    }
    vars.push_back(d_vars[d_last_perm[i]]);
  }
}

bool EnumStreamPermutation::PermutationState::getNextPermutation()
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

EnumStreamSubstitution::EnumStreamSubstitution(quantifiers::TermDbSygus* tds)
    : d_tds(tds), d_stream_permutations(tds), d_curr_ind(0)
{
}

void EnumStreamSubstitution::initialize(TypeNode tn)
{
  d_tn = tn;
  // get variables in value's type
  Node var_list = tn.getDType().getSygusVarList();
  // get subtypes in value's type
  NodeManager* nm = NodeManager::currentNM();
  SygusTypeInfo& ti = d_tds->getTypeInfo(tn);
  std::vector<TypeNode> sf_types;
  ti.getSubfieldTypes(sf_types);
  // associate variables with constructors in all subfield types
  for (const Node& v : var_list)
  {
    // collect constructors for variable in all subtypes
    for (const TypeNode& stn : sf_types)
    {
      const DType& dt = stn.getDType();
      for (unsigned i = 0, size = dt.getNumConstructors(); i < size; ++i)
      {
        if (dt[i].getNumArgs() == 0 && dt[i].getSygusOp() == v)
        {
          d_var_tn_cons[v][stn] =
              nm->mkNode(APPLY_CONSTRUCTOR, dt[i].getConstructor());
        }
      }
    }
  }
  // split initial variables into classes
  for (const Node& v : var_list)
  {
    Assert(ti.getSubclassForVar(v) > 0);
    d_var_classes[ti.getSubclassForVar(v)].push_back(v);
  }
}

void EnumStreamSubstitution::resetValue(Node value)
{
  if (Trace.isOn("synth-stream-concrete"))
  {
    std::stringstream ss;
    Printer::getPrinter(options::outputLanguage())->toStreamSygus(ss, value);
    Trace("synth-stream-concrete")
        << " * Streaming concrete: registering value " << ss.str() << "\n";
  }
  d_last = Node::null();
  d_value = value;
  // reset permutation util
  d_stream_permutations.reset(value);
  // reset combination utils
  d_curr_ind = 0;
  d_comb_state_class.clear();
  Trace("synth-stream-concrete") << " ..combining vars  :";
  for (const std::pair<unsigned, std::vector<Node>>& p : d_var_classes)
  {
    // ignore classes without variables being permuted
    unsigned perm_var_class_sz = d_stream_permutations.getVarClassSize(p.first);
    if (perm_var_class_sz == 0)
    {
      continue;
    }
    d_comb_state_class.push_back(CombinationState(
        p.second.size(), perm_var_class_sz, p.first, p.second));
    if (Trace.isOn("synth-stream-concrete"))
    {
      Trace("synth-stream-concrete")
          << " " << p.first << " -> " << perm_var_class_sz << " from [ ";
      for (const Node& var : p.second)
      {
        std::stringstream ss;
        Printer::getPrinter(options::outputLanguage())->toStreamSygus(ss, var);
        Trace("synth-stream-concrete") << " " << ss.str();
      }
      Trace("synth-stream-concrete") << " ]";
    }
  }
  Trace("synth-stream-concrete") << "\n";
}

Node EnumStreamSubstitution::getNext()
{
  if (Trace.isOn("synth-stream-concrete"))
  {
    std::stringstream ss;
    Printer::getPrinter(options::outputLanguage())->toStreamSygus(ss, d_value);
    Trace("synth-stream-concrete")
        << " ..streaming next combination of " << ss.str() << "\n";
  }
  unsigned n_classes = d_comb_state_class.size();
  // intial case
  if (d_last.isNull())
  {
    d_last = d_stream_permutations.getNext();
  }
  else
  {
    bool new_comb = false;
    while (!new_comb && d_curr_ind < n_classes)
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
    }
    // no new combination
    if (!new_comb)
    {
      Trace("synth-stream-concrete")
          << " ..no new comb, get next permutation\n ....total combs until "
             "here : "
          << d_comb_values.size() << "\n";
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
  if (Trace.isOn("synth-stream-concrete-debug"))
  {
    std::stringstream ss;
    Printer::getPrinter(options::outputLanguage())->toStreamSygus(ss, d_last);
    Trace("synth-stream-concrete-debug")
        << " ..using base perm " << ss.str() << "\n";
  }
  // building substitution
  std::vector<Node> domain_sub, range_sub;
  for (unsigned i = 0, size = d_comb_state_class.size(); i < size; ++i)
  {
    Trace("synth-stream-concrete")
        << " ..comb for class " << d_comb_state_class[i].getSubclassId()
        << " is";
    std::vector<Node> raw_sub;
    d_comb_state_class[i].getLastComb(raw_sub);
    // retrieve variables for substitution domain
    const std::vector<Node>& domain_sub_class =
        d_stream_permutations.getVarsClass(
            d_comb_state_class[i].getSubclassId());
    Assert(domain_sub_class.size() == raw_sub.size());
    // build proper substitution based on variables types and constructors
    for (unsigned j = 0, size_j = raw_sub.size(); j < size_j; ++j)
    {
      for (std::pair<const TypeNode, Node>& p :
           d_var_tn_cons[domain_sub_class[j]])
      {
        // get constructor of type p.first from variable being permuted
        domain_sub.push_back(p.second);
        // get constructor of type p.first from variable to be permuted for
        range_sub.push_back(d_var_tn_cons[raw_sub[j]][p.first]);
        Trace("synth-stream-concrete-debug2")
            << "\n ....{ adding " << domain_sub.back() << " ["
            << domain_sub.back().getType() << "] -> " << range_sub.back()
            << " [" << range_sub.back().getType() << "] }";
      }
    }
    Trace("synth-stream-concrete") << "\n";
  }
  Node comb_value = d_last.substitute(
      domain_sub.begin(), domain_sub.end(), range_sub.begin(), range_sub.end());
  // the new combination value should be fresh, modulo rewriting, by
  // construction (unless it's equiv to a constant, e.g. true / false)
  Node builtin_comb_value =
      d_tds->sygusToBuiltin(comb_value, comb_value.getType());
  if (options::sygusSymBreakDynamic())
  {
    builtin_comb_value =
        d_tds->getExtRewriter()->extendedRewrite(builtin_comb_value);
  }
  if (Trace.isOn("synth-stream-concrete"))
  {
    std::stringstream ss;
    Printer::getPrinter(options::outputLanguage())
        ->toStreamSygus(ss, comb_value);
    Trace("synth-stream-concrete")
        << " ....register new comb value " << ss.str()
        << " with rewritten form " << builtin_comb_value
        << (builtin_comb_value.isConst() ? " (isConst)" : "") << "\n";
  }
  if (!builtin_comb_value.isConst()
      && !d_comb_values.insert(builtin_comb_value).second)
  {
    std::stringstream ss, ss1;
    Printer::getPrinter(options::outputLanguage())
        ->toStreamSygus(ss, comb_value);
    Trace("synth-stream-concrete")
        << " ..term " << ss.str() << " is REDUNDANT with " << builtin_comb_value
        << "\n ..excluding all other concretizations (had "
        << d_comb_values.size() << " already)\n\n";
    return Node::null();
  }
  if (Trace.isOn("synth-stream-concrete"))
  {
    std::stringstream ss;
    Printer::getPrinter(options::outputLanguage())
        ->toStreamSygus(ss, comb_value);
    Trace("synth-stream-concrete")
        << " ..return new comb " << ss.str() << "\n\n";
  }
  return comb_value;
}

EnumStreamSubstitution::CombinationState::CombinationState(
    unsigned n, unsigned k, unsigned subclass_id, const std::vector<Node>& vars)
    : d_n(n), d_k(k)
{
  Assert(!vars.empty());
  Assert(k <= n);
  d_last_comb.resize(k);
  std::iota(d_last_comb.begin(), d_last_comb.end(), 0);
  d_vars = vars;
  d_subclass_id = subclass_id;
}

const unsigned EnumStreamSubstitution::CombinationState::getSubclassId() const
{
  return d_subclass_id;
}

void EnumStreamSubstitution::CombinationState::reset()
{
  std::iota(d_last_comb.begin(), d_last_comb.end(), 0);
}

void EnumStreamSubstitution::CombinationState::getLastComb(
    std::vector<Node>& vars)
{
  for (unsigned i = 0, size = d_last_comb.size(); i < size; ++i)
  {
    if (Trace.isOn("synth-stream-concrete"))
    {
      std::stringstream ss;
      Printer::getPrinter(options::outputLanguage())
          ->toStreamSygus(ss, d_vars[d_last_comb[i]]);
      Trace("synth-stream-concrete") << " " << ss.str();
    }
    vars.push_back(d_vars[d_last_comb[i]]);
  }
}

bool EnumStreamSubstitution::CombinationState::getNextCombination()
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

void EnumStreamConcrete::initialize(Node e) { d_ess.initialize(e.getType()); }
void EnumStreamConcrete::addValue(Node v)
{
  d_ess.resetValue(v);
  d_currTerm = d_ess.getNext();
}
bool EnumStreamConcrete::increment()
{
  d_currTerm = d_ess.getNext();
  return !d_currTerm.isNull();
}
Node EnumStreamConcrete::getCurrent() { return d_currTerm; }
}  // namespace quantifiers
}  // namespace theory
}  // namespace CVC4
