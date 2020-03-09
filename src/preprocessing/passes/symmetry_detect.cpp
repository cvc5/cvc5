/*********************                                                        */
/*! \file symmetry_detect.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Paul Meng
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Symmetry detection module
 **/

#include "preprocessing/passes/symmetry_detect.h"

#include "expr/node_algorithm.h"
#include "theory/quantifiers/alpha_equivalence.h"
#include "theory/quantifiers/term_util.h"
#include "theory/rewriter.h"

using namespace std;
using namespace CVC4::kind;

namespace CVC4 {
namespace preprocessing {
namespace passes {
namespace symbreak {

/** returns n choose k, that is, n!/(k! * (n-k)!) */
unsigned nChoosek(unsigned n, unsigned k)
{
  if (k > n) return 0;
  if (k * 2 > n) k = n - k;
  if (k == 0) return 1;

  int result = n;
  for (int i = 2; i <= static_cast<int>(k); ++i)
  {
    result *= (n - i + 1);
    result /= i;
  }
  return result;
}

/** mk associative node
 *
 * This returns (a normal form for) the term <k>( children ), where
 * k is an associative operator. We return a right-associative
 * chain, since some operators (e.g. set union) require this.
 */
Node mkAssociativeNode(Kind k, std::vector<Node>& children)
{
  Assert(!children.empty());
  NodeManager* nm = NodeManager::currentNM();
  // sort and make right-associative chain
  bool isComm = theory::quantifiers::TermUtil::isComm(k);
  if (isComm)
  {
    std::sort(children.begin(), children.end());
  }
  Node sn;
  for (const Node& sc : children)
  {
    Assert(!sc.isNull());
    if (sn.isNull())
    {
      sn = sc;
    }
    else
    {
      Assert(!isComm || sc.getType().isComparableTo(sn.getType()));
      sn = nm->mkNode(k, sc, sn);
    }
  }
  return sn;
}

void Partition::printPartition(const char* c, Partition p)
{
  for (map<Node, vector<Node> >::iterator sub_vars_it =
           p.d_subvar_to_vars.begin();
       sub_vars_it != p.d_subvar_to_vars.end();
       ++sub_vars_it)
  {
    Trace(c) << "[sym-dt] Partition: " << sub_vars_it->first << " -> {";

    for (vector<Node>::iterator part_it = (sub_vars_it->second).begin();
         part_it != (sub_vars_it->second).end();
         ++part_it)
    {
      Trace(c) << " " << *part_it;
    }
    Trace(c) << " }" << endl;
  }
}

void Partition::addVariable(Node sv, Node v)
{
  d_subvar_to_vars[sv].push_back(v);
  Assert(d_var_to_subvar.find(v) == d_var_to_subvar.end());
  d_var_to_subvar[v] = sv;
}

void Partition::removeVariable(Node sv)
{
  std::map<Node, std::vector<Node> >::iterator its = d_subvar_to_vars.find(sv);
  Assert(its != d_subvar_to_vars.end());
  for (const Node& v : its->second)
  {
    Assert(d_var_to_subvar.find(v) != d_var_to_subvar.end());
    d_var_to_subvar.erase(v);
  }
  d_subvar_to_vars.erase(sv);
}

void Partition::normalize()
{
  for (std::pair<const Node, std::vector<Node> > p : d_subvar_to_vars)
  {
    std::sort(p.second.begin(), p.second.end());
  }
}
void Partition::getVariables(std::vector<Node>& vars)
{
  for (const std::pair<const Node, Node>& p : d_var_to_subvar)
  {
    vars.push_back(p.first);
  }
}

void Partition::getSubstitution(std::vector<Node>& vars,
                                std::vector<Node>& subs)
{
  for (const std::pair<const Node, Node>& p : d_var_to_subvar)
  {
    vars.push_back(p.first);
    subs.push_back(p.second);
  }
}

void PartitionMerger::initialize(Kind k,
                                 const std::vector<Partition>& partitions,
                                 const std::vector<unsigned>& indices)
{
  d_kind = k;
  Trace("sym-dt-debug") << "Initialize partition merger..." << std::endl;
  Trace("sym-dt-debug") << "Count variable occurrences..." << std::endl;
  for (unsigned index : indices)
  {
    d_indices.push_back(index);
    const Partition& p = partitions[index];
    const std::vector<Node>& svs = p.d_subvar_to_vars.begin()->second;
    for (const Node& v : svs)
    {
      if (d_occurs_count.find(v) == d_occurs_count.end())
      {
        d_occurs_count[v] = 1;
      }
      else
      {
        d_occurs_count[v]++;
      }
      d_occurs_by[index][v] = d_occurs_count[v] - 1;
    }
  }
  if (Trace.isOn("sym-dt-debug"))
  {
    Trace("sym-dt-debug") << "    variable occurrences: " << std::endl;
    for (const std::pair<const Node, unsigned>& o : d_occurs_count)
    {
      Trace("sym-dt-debug")
          << "     " << o.first << " -> " << o.second << std::endl;
    }
  }
}

bool PartitionMerger::merge(std::vector<Partition>& partitions,
                            unsigned base_index,
                            std::unordered_set<unsigned>& active_indices,
                            std::vector<unsigned>& merged_indices)
{
  Assert(base_index < partitions.size());
  d_master_base_index = base_index;
  Partition& p = partitions[base_index];
  Trace("sym-dt-debug") << "   try basis index " << base_index
                        << " (#vars = " << p.d_subvar_to_vars.size() << ")"
                        << std::endl;
  Assert(p.d_subvar_to_vars.size() == 1);
  std::vector<Node>& svs = p.d_subvar_to_vars.begin()->second;
  Trace("sym-dt-debug") << "   try basis: " << svs << std::endl;
  // try to merge variables one-by-one
  d_base_indices.clear();
  d_base_indices.insert(base_index);
  d_base_vars.clear();
  d_base_vars.insert(svs.begin(), svs.end());
  d_num_new_indices_needed = d_base_vars.size();
  bool merged = false;
  bool success = false;
  unsigned base_choose = d_base_vars.size() - 1;
  unsigned base_occurs_req = d_base_vars.size();
  do
  {
    Trace("sym-dt-debug") << "   base variables must occur " << base_occurs_req
                          << " times." << std::endl;
    // check if all the base_vars occur at least the required number of times
    bool var_ok = true;
    for (const Node& v : d_base_vars)
    {
      if (d_occurs_count[v] < base_occurs_req)
      {
        Trace("sym-dt-debug") << "...failed variable " << v << std::endl;
        var_ok = false;
        break;
      }
    }
    if (!var_ok)
    {
      // cannot merge due to a base variable
      break;
    }
    // try to find a new variable to merge
    Trace("sym-dt-debug") << "   must find " << d_num_new_indices_needed
                          << " new indices to merge." << std::endl;
    std::vector<unsigned> new_indices;
    Node merge_var;
    d_merge_var_tried.clear();
    if (mergeNewVar(0, new_indices, merge_var, 0, partitions, active_indices))
    {
      if (Trace.isOn("sym-dt-debug"))
      {
        Trace("sym-dt-debug")
            << "   ...merged: " << merge_var << " from indices [ ";
        for (unsigned ni : new_indices)
        {
          Trace("sym-dt-debug") << ni << " ";
        }
        Trace("sym-dt-debug") << "]" << std::endl;
      }
      merged_indices.insert(
          merged_indices.end(), new_indices.begin(), new_indices.end());
      Assert(!merge_var.isNull());
      merged = true;
      success = true;
      // update the number of new indicies needed
      if (base_choose > 0)
      {
        d_num_new_indices_needed +=
            nChoosek(d_base_vars.size(), base_choose - 1);
        // TODO (#2198): update base_occurs_req
      }
    }
    else
    {
      Trace("sym-dt-debug") << "   ...failed to merge" << std::endl;
      success = false;
    }
  } while (success);
  return merged;
}

bool PartitionMerger::mergeNewVar(unsigned curr_index,
                                  std::vector<unsigned>& new_indices,
                                  Node& merge_var,
                                  unsigned num_merge_var_max,
                                  std::vector<Partition>& partitions,
                                  std::unordered_set<unsigned>& active_indices)
{
  Assert(new_indices.size() < d_num_new_indices_needed);
  if (curr_index == d_indices.size())
  {
    return false;
  }
  Trace("sym-dt-debug2") << "merge " << curr_index << " / " << d_indices.size()
                         << ", merge var : " << merge_var
                         << ", upper bound for #occ of merge_var : "
                         << num_merge_var_max << std::endl;
  // try to include this index
  unsigned index = d_indices[curr_index];

  // if not already included
  if (d_base_indices.find(index) == d_base_indices.end())
  {
    Assert(active_indices.find(index) != active_indices.end());
    // check whether it can merge
    Partition& p = partitions[index];
    Trace("sym-dt-debug2") << "current term is " << p.d_term << std::endl;
    Assert(p.d_subvar_to_vars.size() == 1);
    std::vector<Node>& svs = p.d_subvar_to_vars.begin()->second;
    bool include_success = true;
    Node curr_merge_var;
    for (const Node& v : svs)
    {
      if (d_base_vars.find(v) == d_base_vars.end() && v != merge_var)
      {
        if (merge_var.isNull() && curr_merge_var.isNull())
        {
          curr_merge_var = v;
        }
        else
        {
          // cannot include
          Trace("sym-dt-debug2") << "...cannot include (new-var)\n";
          include_success = false;
          curr_merge_var = Node::null();
          break;
        }
      }
    }
    if (!curr_merge_var.isNull())
    {
      // compute the maximum number of indices we can include for v
      Assert(d_occurs_by[index].find(curr_merge_var)
             != d_occurs_by[index].end());
      Assert(d_occurs_count.find(curr_merge_var) != d_occurs_count.end());
      unsigned num_v_max =
          d_occurs_count[curr_merge_var] - d_occurs_by[index][curr_merge_var];
      if (num_v_max >= d_num_new_indices_needed)
      {
        // have we already tried this merge_var?
        if (d_merge_var_tried.find(curr_merge_var) != d_merge_var_tried.end())
        {
          include_success = false;
          Trace("sym-dt-debug2")
              << "...cannot include (already tried new merge var "
              << curr_merge_var << ")\n";
        }
        else
        {
          Trace("sym-dt-debug2")
              << "set merge var : " << curr_merge_var << std::endl;
          d_merge_var_tried.insert(curr_merge_var);
          num_merge_var_max = num_v_max;
          merge_var = curr_merge_var;
        }
      }
      else
      {
        Trace("sym-dt-debug2")
            << "...cannot include (not enough room for new merge var "
            << num_v_max << "<" << d_num_new_indices_needed << ")\n";
        include_success = false;
      }
    }
    else if (!merge_var.isNull()
             && p.d_var_to_subvar.find(merge_var) != p.d_var_to_subvar.end())
    {
      // decrement
      num_merge_var_max--;
      if (num_merge_var_max < d_num_new_indices_needed - new_indices.size())
      {
        Trace("sym-dt-debug2") << "...fail (out of merge var)\n";
        return false;
      }
    }

    if (include_success)
    {
      // try with the index included
      new_indices.push_back(index);

      // do we have enough now?
      if (new_indices.size() == d_num_new_indices_needed)
      {
        std::vector<Node> children;
        children.push_back(p.d_term);
        std::vector<Node> schildren;
        schildren.push_back(p.d_sterm);
        // can now include in the base
        d_base_vars.insert(merge_var);
        Trace("sym-dt-debug") << "found symmetry : { ";
        for (unsigned i : new_indices)
        {
          Assert(d_base_indices.find(i) == d_base_indices.end());
          d_base_indices.insert(i);
          Trace("sym-dt-debug") << i << " ";
          const Partition& p2 = partitions[i];
          children.push_back(p2.d_term);
          schildren.push_back(p2.d_sterm);
          Assert(active_indices.find(i) != active_indices.end());
          active_indices.erase(i);
        }
        Trace("sym-dt-debug") << "}" << std::endl;
        Trace("sym-dt-debug") << "Reconstruct master partition "
                              << d_master_base_index << std::endl;
        Partition& p3 = partitions[d_master_base_index];
        // reconstruct the master partition
        p3.d_term = mkAssociativeNode(d_kind, children);
        p3.d_sterm = mkAssociativeNode(d_kind, schildren);
        Assert(p3.d_subvar_to_vars.size() == 1);
        Node sb_v = p3.d_subvar_to_vars.begin()->first;
        Trace("sym-dt-debug") << "- set var to svar: " << merge_var << " -> "
                              << sb_v << std::endl;
        p3.addVariable(sb_v, merge_var);
        return true;
      }
      if (mergeNewVar(curr_index + 1,
                      new_indices,
                      merge_var,
                      num_merge_var_max,
                      partitions,
                      active_indices))
      {
        return true;
      }
      new_indices.pop_back();
      // if we included with the merge var, no use trying not including
      if (curr_merge_var.isNull() && !merge_var.isNull())
      {
        Trace("sym-dt-debug2") << "...fail (failed merge var)\n";
        return false;
      }
    }
  }
  // TODO (#2198):
  // if we haven't yet chosen a merge variable, we may not have enough elements
  // left in d_indices.

  // try with it not included
  return mergeNewVar(curr_index + 1,
                     new_indices,
                     merge_var,
                     num_merge_var_max,
                     partitions,
                     active_indices);
}

SymmetryDetect::SymmetryDetect() : d_tsym_id_counter(1)
{
  d_trueNode = NodeManager::currentNM()->mkConst<bool>(true);
  d_falseNode = NodeManager::currentNM()->mkConst<bool>(false);
}

Partition SymmetryDetect::detect(const vector<Node>& assertions)
{
  Node an;
  if (assertions.empty())
  {
    an = d_trueNode;
  }
  else if (assertions.size() == 1)
  {
    an = assertions[0];
  }
  else
  {
    an = NodeManager::currentNM()->mkNode(kind::AND, assertions);
  }
  Partition p = findPartitions(an);
  Trace("sym-dt") << endl
                  << "------------------------------ The Final Partition "
                     "------------------------------"
                  << endl;
  if(Trace.isOn("sym-dt"))
  {
    Partition::printPartition("sym-dt", p);
  }
  return p;
}

Node SymmetryDetect::getSymBreakVariable(TypeNode tn, unsigned index)
{
  std::map<TypeNode, std::vector<Node> >::iterator it = d_sb_vars.find(tn);
  if (it == d_sb_vars.end())
  {
    // initialize the variables for type tn
    d_sb_vars[tn].clear();
    it = d_sb_vars.find(tn);
  }
  NodeManager* nm = NodeManager::currentNM();
  while (it->second.size() <= index)
  {
    std::stringstream ss;
    ss << "_sym_bk_" << tn << "_" << (it->second.size() + 1);
    Node fresh_var = nm->mkBoundVar(ss.str(), tn);
    it->second.push_back(fresh_var);
  }
  return it->second[index];
}

Node SymmetryDetect::getSymBreakVariableInc(TypeNode tn,
                                            std::map<TypeNode, unsigned>& index)
{
  // ensure we use a new index for this variable
  unsigned new_index = 0;
  std::map<TypeNode, unsigned>::iterator itt = index.find(tn);
  if (itt != index.end())
  {
    new_index = itt->second;
  }
  index[tn] = new_index + 1;
  return getSymBreakVariable(tn, new_index);
}

void SymmetryDetect::compute(std::vector<std::vector<Node> >& part,
                             const std::vector<Node>& assertions)
{
  Partition p = detect(assertions);

  std::vector<std::vector<Node> > parts;
  for (map<Node, vector<Node> >::const_iterator subvar_to_vars_it =
           p.d_subvar_to_vars.begin();
       subvar_to_vars_it != p.d_subvar_to_vars.end();
       ++subvar_to_vars_it)
  {
    parts.push_back(subvar_to_vars_it->second);
  }
}
void SymmetryDetect::computeTerms(std::vector<std::vector<Node> >& sterms,
                                  const std::vector<Node>& assertions)
{
  Partition p = detect(assertions);

  for (const std::pair<const Node, std::vector<Node> > sp : p.d_subvar_to_vars)
  {
    if (sp.second.size() > 1)
    {
      // A naive method would do sterms.push_back(sp.second), that is, say that
      // the variables themselves are symmetric terms. However, the following
      // code finds some subterms of assertions that are symmetric under this
      // set in the variable partition. For example, for the input:
      //   f(x)+f(y) >= 0
      // naively {x, y} are reported as symmetric terms, but below ensures we
      // say {f(x), f(y)} are reported as symmetric terms instead.
      Node sv = sp.first;
      Trace("sym-dt-tsym-cons")
          << "Construct term symmetry from " << sp.second << "..." << std::endl;
      // choose an arbitrary term symmetry
      std::vector<unsigned>& tsids = d_var_to_tsym_ids[sp.second[0]];
      if (tsids.empty())
      {
        // no (ground) term symmetries, just use naive
        sterms.push_back(sp.second);
      }
      else
      {
        unsigned tsymId = tsids[tsids.size() - 1];
        Trace("sym-dt-tsym-cons") << "...use tsym id " << tsymId << std::endl;
        // get the substitution
        std::vector<Node> vars;
        std::vector<Node> subs;
        for (const Node& v : sp.second)
        {
          vars.push_back(v);
          subs.push_back(sv);
        }
        std::vector<Node>& tsym = d_tsyms[tsymId];
        // map terms in this symmetry to their final form
        std::vector<unsigned> tsym_indices;
        std::vector<Node> tsym_terms;
        for (unsigned j = 0, size = tsym.size(); j < size; j++)
        {
          Node tst = tsym[j];
          Node tsts = tst.substitute(
              vars.begin(), vars.end(), subs.begin(), subs.end());
          tsym_indices.push_back(j);
          tsym_terms.push_back(tsts);
        }
        // take into account alpha-equivalence
        std::map<Node, std::vector<unsigned> > t_to_st;
        computeAlphaEqTerms(tsym_indices, tsym_terms, t_to_st);
        Node tshUse;
        for (const std::pair<const Node, std::vector<unsigned> >& tsh : t_to_st)
        {
          Trace("sym-dt-tsym-cons-debug")
              << "  " << tsh.first << " -> #" << tsh.second.size() << std::endl;
          if (tsh.second.size() > 1)
          {
            tshUse = tsh.first;
            break;
          }
        }
        if (!tshUse.isNull())
        {
          std::vector<Node> tsymCons;
          for (unsigned j : t_to_st[tshUse])
          {
            tsymCons.push_back(tsym[j]);
          }
          Trace("sym-dt-tsym-cons") << "...got " << tsymCons << std::endl;
          sterms.push_back(tsymCons);
        }
      }
    }
  }
}

/**
 * We build the partition trie indexed by
 * parts[0].var_to_subvar[v]....parts[n].var_to_subvar[v]. The leaves of a
 * partition trie are the new regions of a partition
 */
class PartitionTrie
{
 public:
  /** Variables at the leave */
  std::vector<Node> d_variables;
  /** The mapping from a node to its children */
  std::map<Node, PartitionTrie> d_children;
};

Partition SymmetryDetect::findPartitions(Node node)
{
  Trace("sym-dt-debug")
      << "------------------------------------------------------------" << endl;
  Trace("sym-dt-debug") << "[sym-dt] findPartitions gets a term: " << node
                        << endl;
  map<Node, Partition>::iterator partition = d_term_partition.find(node);

  // Return its partition from cache if we have processed the node before
  if (partition != d_term_partition.end())
  {
    Trace("sym-dt-debug") << "[sym-dt] We have seen the node " << node
                          << " before, thus we return its partition from cache."
                          << endl;
    return partition->second;
  }

  // The new partition for node
  Partition p;
  // If node is a variable
  if (node.isVar() && node.getKind() != kind::BOUND_VARIABLE)
  {
    TypeNode type = node.getType();
    Node fresh_var = getSymBreakVariable(type, 0);
    p.d_term = node;
    p.d_sterm = fresh_var;
    p.addVariable(fresh_var, node);
    d_term_partition[node] = p;
    return p;
  }
  // If node is a constant
  else if (node.getNumChildren() == 0)
  {
    p.d_term = node;
    p.d_sterm = node;
    d_term_partition[node] = p;
    return p;
  }
  NodeManager* nm = NodeManager::currentNM();

  Kind k = node.getKind();
  bool isAssocComm = false;
  // EQUAL is a special case here: we consider EQUAL to be associative,
  // and handle the type polymorphism specially.
  bool isAssoc = k == kind::EQUAL || theory::quantifiers::TermUtil::isAssoc(k);
  // for now, only consider commutative operators that are also associative
  if (isAssoc)
  {
    isAssocComm = theory::quantifiers::TermUtil::isComm(k);
  }

  // Get all children of node
  Trace("sym-dt-debug") << "[sym-dt] collectChildren for: " << node
                        << " with kind " << node.getKind() << endl;
  // Children of node
  std::vector<Node> children;
  bool operatorChild = false;
  if (node.getKind() == APPLY_UF)
  {
    // compute for the operator
    children.push_back(node.getOperator());
    operatorChild = true;
  }
  if (!isAssocComm)
  {
    children.insert(children.end(), node.begin(), node.end());
  }
  else
  {
    collectChildren(node, children);
  }
  Trace("sym-dt-debug") << "[sym-dt] children: " << children << endl;

  // Partitions of children
  std::vector<Partition> partitions;
  // Create partitions for children
  std::unordered_set<unsigned> active_indices;
  for (const Node& c : children)
  {
    active_indices.insert(partitions.size());
    partitions.push_back(findPartitions(c));
  }
  if (Trace.isOn("sym-dt-debug"))
  {
    Trace("sym-dt-debug") << "----------------------------- Start processing "
                             "partitions for "
                          << node << " -------------------------------" << endl;
    for (unsigned j = 0, size = partitions.size(); j < size; j++)
    {
      Trace("sym-dt-debug") << "[" << j << "]: " << partitions[j].d_term
                            << " --> " << partitions[j].d_sterm << std::endl;
    }
    Trace("sym-dt-debug") << "-----------------------------" << std::endl;
  }

  if (isAssocComm)
  {
    // get the list of indices and terms
    std::vector<unsigned> indices;
    std::vector<Node> sterms;
    for (unsigned j = 0, size = partitions.size(); j < size; j++)
    {
      Node st = partitions[j].d_sterm;
      if (!st.isNull())
      {
        indices.push_back(j);
        sterms.push_back(st);
      }
    }
    // now, compute terms to indices
    std::map<Node, std::vector<unsigned> > sterm_to_indices;
    computeAlphaEqTerms(indices, sterms, sterm_to_indices);

    for (const std::pair<Node, std::vector<unsigned> >& sti : sterm_to_indices)
    {
      Node cterm = sti.first;
      if (Trace.isOn("sym-dt-debug"))
      {
        Trace("sym-dt-debug") << "  indices[" << cterm << "] = ";
        for (unsigned i : sti.second)
        {
          Trace("sym-dt-debug") << i << " ";
        }
        Trace("sym-dt-debug") << std::endl;
      }
      // merge children, remove active indices
      std::vector<Node> fixedSVar;
      std::vector<Node> fixedVar;
      processPartitions(
          k, partitions, sti.second, active_indices, fixedSVar, fixedVar);
    }
  }
  // initially set substituted term to node
  p.d_sterm = node;
  // for all active indices
  vector<Node> all_vars;
  for (unsigned i : active_indices)
  {
    Trace("sym-dt-debug") << "Reconstruct partition for active index : " << i
                          << std::endl;
    Partition& pa = partitions[i];
    // add to overall list of variables
    for (const pair<const Node, vector<Node> >& pas : pa.d_subvar_to_vars)
    {
      Trace("sym-dt-debug")
          << "...process " << pas.first << " -> " << pas.second << std::endl;
      // add all vars to partition trie classifier
      for (const Node& c : pas.second)
      {
        if (std::find(all_vars.begin(), all_vars.end(), c) == all_vars.end())
        {
          all_vars.push_back(c);
        }
      }
    }
    Trace("sym-dt-debug") << "...term : " << pa.d_sterm << std::endl;
  }

  PartitionTrie pt;
  std::map<TypeNode, unsigned> type_index;
  type_index.clear();
  // the indices we need to reconstruct
  std::map<unsigned, bool> rcons_indices;
  // Build the partition trie
  std::sort(all_vars.begin(), all_vars.end());
  // for each variable
  for (const Node& n : all_vars)
  {
    Trace("sym-dt-debug") << "[sym-dt] Add a variable {" << n
                          << "} to the partition trie, #partitions = "
                          << active_indices.size() << "..." << endl;
    std::vector<Node> subvars;
    std::vector<unsigned> useVarInd;
    Node useVar;
    for (unsigned i : active_indices)
    {
      Partition& pa = partitions[i];
      std::map<Node, Node>::iterator var_sub_it = pa.d_var_to_subvar.find(n);
      if (var_sub_it != pa.d_var_to_subvar.end())
      {
        Node v = var_sub_it->second;
        subvars.push_back(v);
        if (useVar.isNull() || v == useVar)
        {
          useVar = v;
          useVarInd.push_back(i);
        }
        else
        {
          // will need to reconstruct the child
          rcons_indices[i] = true;
        }
      }
      else
      {
        subvars.push_back(Node::null());
      }
    }
    // all variables should occur in at least one child
    Assert(!useVar.isNull());
    Trace("sym-dt-debug")
        << "[sym-dt] Symmetry breaking variables for the variable " << n << ": "
        << subvars << endl;
    // add to the trie
    PartitionTrie* curr = &pt;
    for (const Node& c : subvars)
    {
      curr = &(curr->d_children[c]);
    }
    curr->d_variables.push_back(n);

    // allocate the necessary variable
    bool usingUseVar = false;
    if (curr->d_variables.size() > 1)
    {
      // must use the previous
      Node an = curr->d_variables[0];
      useVar = p.d_var_to_subvar[an];
      Trace("sym-dt-debug") << "...use var from " << an << "." << std::endl;
    }
    else if (useVar.isNull()
             || p.d_subvar_to_vars.find(useVar) != p.d_subvar_to_vars.end())
    {
      Trace("sym-dt-debug") << "...allocate new var." << std::endl;
      // must allocate new
      TypeNode ntn = n.getType();
      do
      {
        useVar = getSymBreakVariableInc(ntn, type_index);
      } while (p.d_subvar_to_vars.find(useVar) != p.d_subvar_to_vars.end());
    }
    else
    {
      Trace("sym-dt-debug") << "...reuse var." << std::endl;
      usingUseVar = true;
    }
    if (!usingUseVar)
    {
      // can't use the useVar, indicate indices for reconstruction
      for (unsigned ui : useVarInd)
      {
        rcons_indices[ui] = true;
      }
    }
    Trace("sym-dt-debug") << "[sym-dt] Map : " << n << " -> " << useVar
                          << std::endl;
    p.addVariable(useVar, n);
  }

  std::vector<Node> pvars;
  std::vector<Node> psubs;
  if (!rcons_indices.empty())
  {
    p.getSubstitution(pvars, psubs);
  }

  // Reconstruct the substituted node
  p.d_term = node;
  std::vector<Node> schildren;
  if (!isAssocComm)
  {
    Assert(active_indices.size() == children.size());
    // order matters, and there is no chance we merged children
    schildren.resize(children.size());
  }
  for (unsigned i : active_indices)
  {
    Partition& pa = partitions[i];
    Node sterm = pa.d_sterm;
    Assert(!sterm.isNull());
    if (rcons_indices.find(i) != rcons_indices.end())
    {
      // must reconstruct via a substitution
      Trace("sym-dt-debug2") << "  reconstruct index " << i << std::endl;
      sterm = pa.d_term.substitute(
          pvars.begin(), pvars.end(), psubs.begin(), psubs.end());
    }
    if (isAssocComm)
    {
      schildren.push_back(sterm);
    }
    else
    {
      Assert(i < schildren.size());
      schildren[i] = sterm;
    }
  }

  Trace("sym-dt-debug") << "[sym-dt] Reconstructing node: " << node
                        << ", #children = " << schildren.size() << "/"
                        << children.size() << endl;
  if (isAssocComm)
  {
    p.d_sterm = mkAssociativeNode(k, schildren);
  }
  else
  {
    if (node.getMetaKind() == metakind::PARAMETERIZED && !operatorChild)
    {
      schildren.insert(schildren.begin(), node.getOperator());
    }
    p.d_sterm = nm->mkNode(k, schildren);
  }
  Trace("sym-dt-debug") << "...return sterm: " << p.d_sterm << std::endl;
  Trace("sym-dt-debug") << ".....types: " << p.d_sterm.getType() << " "
                        << node.getType() << std::endl;
  Assert(p.d_sterm.getType() == node.getType());

  // normalize: ensures that variable lists are sorted
  p.normalize();
  d_term_partition[node] = p;
  Partition::printPartition("sym-dt-debug", p);
  return p;
}

void SymmetryDetect::collectChildren(Node node, vector<Node>& children)
{
  Kind k = node.getKind();
  Assert((k == kind::EQUAL || theory::quantifiers::TermUtil::isAssoc(k))
         && theory::quantifiers::TermUtil::isComm(k));

  // must track the type of the children we are collecting
  // this is to avoid having vectors of children with different type, like
  // (= (= x 0) (= y "abc"))
  TypeNode ctn = node[0].getType();

  Node cur;
  vector<Node> visit;
  visit.push_back(node);
  unordered_set<Node, NodeHashFunction> visited;

  do
  {
    cur = visit.back();
    visit.pop_back();
    if (visited.find(cur) == visited.end())
    {
      visited.insert(cur);
      if (cur.getNumChildren() > 0 && cur.getKind() == k
          && cur[0].getType() == ctn)
      {
        for (const Node& cn : cur)
        {
          visit.push_back(cn);
        }
      }
      else
      {
        children.push_back(cur);
      }
    }
  } while (!visit.empty());
}

void SymmetryDetect::computeAlphaEqTerms(
    const std::vector<unsigned>& indices,
    const std::vector<Node>& sterms,
    std::map<Node, std::vector<unsigned> >& sterm_to_indices)
{
  Assert(indices.size() == sterms.size());
  // also store quantified formulas, since these may be alpha-equivalent
  std::vector<unsigned> quant_sterms;
  for (unsigned j = 0, size = indices.size(); j < size; j++)
  {
    Node st = sterms[j];
    Assert(!st.isNull());
    if (st.getKind() == FORALL)
    {
      quant_sterms.push_back(j);
    }
    else
    {
      sterm_to_indices[st].push_back(indices[j]);
    }
  }
  // process the quantified formulas
  if (quant_sterms.size() == 1)
  {
    // only one quantified formula, won't be alpha equivalent
    unsigned j = quant_sterms[0];
    sterm_to_indices[sterms[j]].push_back(indices[j]);
  }
  else if (!quant_sterms.empty())
  {
    theory::quantifiers::AlphaEquivalenceDb aedb(&d_tcanon);
    for (unsigned j : quant_sterms)
    {
      // project via alpha equivalence
      Node st = sterms[j];
      Node st_ae = aedb.addTerm(st);
      sterm_to_indices[st_ae].push_back(indices[j]);
    }
  }
}

/** A basic trie for storing vectors of arguments */
class NodeTrie
{
 public:
  NodeTrie() {}
  /** value at this node*/
  std::vector<unsigned> d_value;
  /** children of this node */
  std::map<Node, NodeTrie> d_children;
  /** clear the children */
  void clear() { d_children.clear(); }
  /**
   * Return true iff we've added the suffix of the vector of arguments starting
   * at index before.
   */
  unsigned add(unsigned value,
               const std::vector<Node>& args,
               unsigned index = 0)
  {
    if (index == args.size())
    {
      d_value.push_back(value);
      return d_value[0];
    }
    return d_children[args[index]].add(value, args, index + 1);
  }
};

void SymmetryDetect::processPartitions(
    Kind k,
    std::vector<Partition>& partitions,
    const std::vector<unsigned>& indices,
    std::unordered_set<unsigned>& active_indices,
    std::vector<Node>& fixedSVar,
    std::vector<Node>& fixedVar)
{
  Assert(!indices.empty());
  unsigned first_index = indices[0];
  if (Trace.isOn("sym-dt-debug"))
  {
    Trace("sym-dt-debug") << "[sym-dt] process partitions for ";
    for (unsigned i : indices)
    {
      Trace("sym-dt-debug") << i << " ";
    }
    Trace("sym-dt-debug") << std::endl;
  }
  unsigned num_sb_vars = partitions[first_index].d_subvar_to_vars.size();
  if (num_sb_vars == 0)
  {
    // no need to merge
    Trace("sym-dt-debug") << "...trivial (no sym vars)" << std::endl;
    return;
  }
  if (num_sb_vars > 1)
  {
    // see if we can drop, e.g. {x}{A}, {x}{B} ---> {A}, {B}

    std::map<Node, NodeTrie> svarTrie;
    std::map<Node, std::map<unsigned, std::vector<unsigned> > > svarEqc;

    for (unsigned j = 0, size = indices.size(); j < size; j++)
    {
      unsigned index = indices[j];
      Partition& p = partitions[index];
      for (const std::pair<const Node, std::vector<Node> > ps :
           p.d_subvar_to_vars)
      {
        Node sv = ps.first;
        unsigned res = svarTrie[sv].add(index, ps.second);
        svarEqc[sv][res].push_back(index);
      }
    }
    Trace("sym-dt-debug")
        << "...multiple symmetry breaking variables, regroup and drop"
        << std::endl;
    unsigned minGroups = indices.size();
    Node svarMin;
    for (const std::pair<const Node,
                         std::map<unsigned, std::vector<unsigned> > > sve :
         svarEqc)
    {
      if (Trace.isOn("sym-dt-debug"))
      {
        Trace("sym-dt-debug") << "For " << sve.first << " : ";
        for (const std::pair<const unsigned, std::vector<unsigned> > svee :
             sve.second)
        {
          Trace("sym-dt-debug") << "{ ";
          for (unsigned i : svee.second)
          {
            Trace("sym-dt-debug") << i << " ";
          }
          Trace("sym-dt-debug") << "}";
        }
      }
      unsigned ngroups = sve.second.size();
      Trace("sym-dt-debug") << ", #groups=" << ngroups << std::endl;
      if (ngroups < minGroups)
      {
        minGroups = ngroups;
        svarMin = sve.first;
        if (minGroups == 1)
        {
          break;
        }
      }
    }
    if (minGroups == indices.size())
    {
      // can only handle symmetries that are classified by { n }
      Trace("sym-dt-debug") << "...failed to merge (multiple symmetry breaking "
                               "vars with no groups)"
                            << std::endl;
      return;
    }
    // recursive call for each group
    for (const std::pair<unsigned, std::vector<unsigned> >& svee :
         svarEqc[svarMin])
    {
      Assert(!svee.second.empty());
      unsigned firstIndex = svee.second[0];
      unsigned nfvars = 0;
      Trace("sym-dt-debug") << "Recurse, fixing " << svarMin << " -> { ";
      // add the list of fixed variables
      for (const Node& v : partitions[firstIndex].d_subvar_to_vars[svarMin])
      {
        Trace("sym-dt-debug") << v << " ";
        fixedSVar.push_back(svarMin);
        fixedVar.push_back(v);
        nfvars++;
      }
      Trace("sym-dt-debug") << "}" << std::endl;

      // remove it from each of the partitions to process
      for (unsigned pindex : svee.second)
      {
        partitions[pindex].removeVariable(svarMin);
      }

      // recursive call
      processPartitions(
          k, partitions, svee.second, active_indices, fixedSVar, fixedVar);

      // remove the list of fixed variables
      for (unsigned i = 0; i < nfvars; i++)
      {
        fixedVar.pop_back();
        fixedSVar.pop_back();
      }
    }
    return;
  }
  // separate by number of variables
  // for each n, nv_indices[n] contains the indices of partitions of the form
  // { w1 -> { x1, ..., xn } }
  std::map<unsigned, std::vector<unsigned> > nv_indices;
  for (unsigned j = 0, size = indices.size(); j < size; j++)
  {
    unsigned index = indices[j];
    Assert(partitions[index].d_subvar_to_vars.size() == 1);
    unsigned num_vars = partitions[index].d_var_to_subvar.size();
    nv_indices[num_vars].push_back(index);
  }
  for (const std::pair<const unsigned, std::vector<unsigned> >& nvi :
       nv_indices)
  {
    if (nvi.second.size() <= 1)
    {
      // no symmetries
      continue;
    }
    unsigned num_vars = nvi.first;
    if (Trace.isOn("sym-dt-debug"))
    {
      Trace("sym-dt-debug") << "    nv_indices[" << num_vars << "] = ";
      for (unsigned i : nvi.second)
      {
        Trace("sym-dt-debug") << i << " ";
      }
      Trace("sym-dt-debug") << std::endl;
    }
    Trace("sym-dt-debug") << "Check for duplicates..." << std::endl;
    // drop duplicates
    // this ensures we don't double count equivalent children that were not
    // syntactically identical e.g. (or (= x y) (= y x))
    NodeTrie ntrie;
    // non-duplicate indices
    std::unordered_set<unsigned> nvis;
    for (unsigned index : nvi.second)
    {
      Partition& p = partitions[index];
      std::vector<Node>& svs = p.d_subvar_to_vars.begin()->second;
      unsigned aindex = ntrie.add(index, svs);
      if (aindex == index)
      {
        nvis.insert(index);
      }
      else if (theory::quantifiers::TermUtil::isNonAdditive(k))
      {
        Trace("sym-dt-debug")
            << "Drop duplicate child : " << index << std::endl;
        Assert(active_indices.find(index) != active_indices.end());
        active_indices.erase(index);
      }
      else
      {
        nvis.erase(aindex);
      }
    }
    std::vector<unsigned> check_indices;
    check_indices.insert(check_indices.end(), nvis.begin(), nvis.end());
    // now, try to merge these partitions
    mergePartitions(k, partitions, check_indices, active_indices);
  }
  // now, re-add the fixed variables
  if (!fixedVar.empty())
  {
    for (unsigned j = 0, size = indices.size(); j < size; j++)
    {
      unsigned index = indices[j];
      // if still active
      if (active_indices.find(index) != active_indices.end())
      {
        for (unsigned i = 0, size2 = fixedSVar.size(); i < size2; i++)
        {
          // add variable
          partitions[index].addVariable(fixedSVar[i], fixedVar[i]);
        }
      }
    }
  }
}

void SymmetryDetect::mergePartitions(
    Kind k,
    std::vector<Partition>& partitions,
    const std::vector<unsigned>& indices,
    std::unordered_set<unsigned>& active_indices)
{
  if (indices.size() <= 1)
  {
    return;
  }
  if (Trace.isOn("sym-dt-debug"))
  {
    Trace("sym-dt-debug") << "--- mergePartitions..." << std::endl;
    Trace("sym-dt-debug") << "  indices ";
    for (unsigned i : indices)
    {
      Trace("sym-dt-debug") << i << " ";
    }
    Trace("sym-dt-debug") << std::endl;
  }
  Assert(!indices.empty());

  // initialize partition merger class
  PartitionMerger pm;
  pm.initialize(k, partitions, indices);

  for (unsigned index : indices)
  {
    Node mterm = partitions[index].d_term;
    std::vector<unsigned> merged_indices;
    if (pm.merge(partitions, index, active_indices, merged_indices))
    {
      // get the symmetric terms, these will be used when doing symmetry
      // breaking
      std::vector<Node> symTerms;
      // include the term from the base index
      symTerms.push_back(mterm);
      for (unsigned mi : merged_indices)
      {
        Node st = partitions[mi].d_term;
        symTerms.push_back(st);
      }
      Trace("sym-dt-debug") << "    ......merged " << symTerms << std::endl;
      std::vector<Node> vars;
      partitions[index].getVariables(vars);
      storeTermSymmetry(symTerms, vars);
      Trace("sym-dt-debug") << "    ......recurse" << std::endl;
      std::vector<unsigned> rem_indices;
      for (unsigned ii : indices)
      {
        if (ii != index && active_indices.find(ii) != active_indices.end())
        {
          rem_indices.push_back(ii);
        }
      }
      mergePartitions(k, partitions, rem_indices, active_indices);
      return;
    }
  }
}

void SymmetryDetect::storeTermSymmetry(const std::vector<Node>& symTerms,
                                       const std::vector<Node>& vars)
{
  Trace("sym-dt-tsym") << "*** Term symmetry : " << symTerms << std::endl;
  Trace("sym-dt-tsym") << "*** Over variables : " << vars << std::endl;
  // cannot have free variable
  if (expr::hasFreeVar(symTerms[0]))
  {
    Trace("sym-dt-tsym") << "...free variable, do not allocate." << std::endl;
    return;
  }

  unsigned tid = d_tsym_id_counter;
  Trace("sym-dt-tsym") << "...allocate id " << tid << std::endl;
  d_tsym_id_counter = d_tsym_id_counter + 1;
  // allocate the term symmetry
  d_tsyms[tid] = symTerms;
  d_tsym_to_vars[tid] = vars;
  for (const Node& v : vars)
  {
    d_var_to_tsym_ids[v].push_back(tid);
  }
}

}  // namespace symbreak
}  // namespace passes
}  // namespace preprocessing
}  // namespace CVC4
