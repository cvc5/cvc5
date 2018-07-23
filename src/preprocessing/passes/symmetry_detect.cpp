/*********************                                                        */
/*! \file symmetry_detect.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Paul Meng
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2018 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Symmetry detection module
 **/

#include "preprocessing/passes/symmetry_detect.h"
#include "theory/quantifiers/term_util.h"
#include "theory/rewriter.h"

using namespace std;

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

void Partition::normalize()
{
  for (std::pair<const Node, std::vector<Node> > p : d_subvar_to_vars)
  {
    std::sort(p.second.begin(), p.second.end());
  }
}

void PartitionMerger::initialize(Kind k,
                                 const std::vector<Partition>& partitions,
                                 const std::vector<unsigned>& indices)
{
  d_kind = k;
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
                            std::unordered_set<unsigned>& active_indices)
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
      Trace("sym-dt-debug") << "   ...merged: " << merge_var << std::endl;
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
                         << std::endl;
  // try to include this index
  unsigned index = d_indices[curr_index];

  // if not already included
  if (d_base_indices.find(index) == d_base_indices.end())
  {
    Assert(active_indices.find(index) != active_indices.end());
    // check whether it can merge
    Partition& p = partitions[index];
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
    else if (!include_success && !merge_var.isNull())
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
        for (const unsigned& i : new_indices)
        {
          Assert(d_base_indices.find(i) == d_base_indices.end());
          d_base_indices.insert(i);
          Trace("sym-dt-debug") << i << " ";
          const Partition& p = partitions[i];
          children.push_back(p.d_term);
          schildren.push_back(p.d_sterm);
          Assert(active_indices.find(i) != active_indices.end());
          active_indices.erase(i);
        }
        Trace("sym-dt-debug") << "}" << std::endl;
        Trace("sym-dt-debug") << "Reconstruct master partition "
                              << d_master_base_index << std::endl;
        Partition& p = partitions[d_master_base_index];
        // reconstruct the master partition
        p.d_term = mkAssociativeNode(d_kind, children);
        p.d_sterm = mkAssociativeNode(d_kind, schildren);
        Assert(p.d_subvar_to_vars.size() == 1);
        Node sb_v = p.d_subvar_to_vars.begin()->first;
        p.d_subvar_to_vars[sb_v].push_back(merge_var);
        Trace("sym-dt-debug") << "- set var to svar: " << merge_var << " -> "
                              << sb_v << std::endl;
        p.d_var_to_subvar[merge_var] = sb_v;
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

void PartitionTrie::getNewPartition(Partition& part,
                                    PartitionTrie& pt,
                                    std::map<Node, Node>& var_to_svar)
{
  if (!pt.d_variables.empty())
  {
    Assert(var_to_svar.find(pt.d_variables[0]) != var_to_svar.end());
    Node svar = var_to_svar[pt.d_variables[0]];
    Trace("sym-dt-debug")
        << "[sym-dt] A partition from leaves of the partition trie:{";
    for (const Node& v : pt.d_variables)
    {
      Trace("sym-dt-debug") << " " << v;
      part.d_var_to_subvar[v] = svar;
      part.d_subvar_to_vars[svar].push_back(v);
    }
    Trace("sym-dt-debug") << " }" << endl;
  }
  else
  {
    for (map<Node, PartitionTrie>::iterator part_it = pt.d_children.begin();
         part_it != pt.d_children.end();
         ++part_it)
    {
      getNewPartition(part, part_it->second, var_to_svar);
    }
  }
}

Node PartitionTrie::addNode(Node target_var, vector<Partition>& partitions)
{
  Trace("sym-dt-debug") << "[sym-dt] Add a variable {" << target_var
                        << "} to the partition trie, #partitions = "
                        << partitions.size() << "..." << endl;
  Assert(!partitions.empty());
  vector<Node> subvars;

  for (vector<Partition>::iterator part_it = partitions.begin();
       part_it != partitions.end();
       ++part_it)
  {
    map<Node, Node>::iterator var_sub_it =
        (*part_it).d_var_to_subvar.find(target_var);

    if (var_sub_it != (*part_it).d_var_to_subvar.end())
    {
      subvars.push_back(var_sub_it->second);
    }
    else
    {
      subvars.push_back(Node::null());
    }
  }

  Trace("sym-dt-debug")
      << "[sym-dt] Symmetry breaking variables for the variable " << target_var
      << ": " << subvars << endl;
  PartitionTrie* curr = this;
  for (const Node& c : subvars)
  {
    curr = &(curr->d_children[c]);
  }
  curr->d_variables.push_back(target_var);
  return curr->d_variables[0];
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
  while (it->second.size() <= index)
  {
    std::stringstream ss;
    ss << "_sym_bk_" << tn << "_" << (it->second.size() + 1);
    Node fresh_var =
        NodeManager::currentNM()->mkSkolem(ss.str(),
                                           tn,
                                           "symmetry breaking variable",
                                           NodeManager::SKOLEM_EXACT_NAME);
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

void SymmetryDetect::getPartition(vector<vector<Node> >& parts,
                                  const vector<Node>& assertions)
{
  Partition p = detect(assertions);

  for (map<Node, vector<Node> >::const_iterator subvar_to_vars_it =
           p.d_subvar_to_vars.begin();
       subvar_to_vars_it != p.d_subvar_to_vars.end();
       ++subvar_to_vars_it)
  {
    parts.push_back(subvar_to_vars_it->second);
  }
}

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
    vector<Node> vars;
    TypeNode type = node.getType();
    Node fresh_var = getSymBreakVariable(type, 0);
    vars.push_back(node);
    p.d_term = node;
    p.d_sterm = fresh_var;
    p.d_subvar_to_vars[fresh_var] = vars;
    p.d_var_to_subvar[node] = fresh_var;
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

  // Children of node
  vector<Node> children;
  // Partitions of children
  vector<Partition> partitions;

  // Get all children of node
  Trace("sym-dt-debug") << "[sym-dt] collectChildren for: " << node
                        << " with operator " << node.getKind() << endl;
  if (!isAssocComm)
  {
    children.insert(children.end(), node.begin(), node.end());
  }
  else
  {
    collectChildren(node, children);
  }
  Trace("sym-dt-debug") << "[sym-dt] children: " << children << endl;

  // Create partitions for children
  std::unordered_set<unsigned> active_indices;
  for (vector<Node>::iterator children_it = children.begin();
       children_it != children.end();
       ++children_it)
  {
    active_indices.insert(partitions.size());
    partitions.push_back(findPartitions(*children_it));
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
    // map substituted terms to indices in partitions
    std::map<Node, std::vector<unsigned> > sterm_to_indices;
    for (unsigned j = 0, size = partitions.size(); j < size; j++)
    {
      if (!partitions[j].d_sterm.isNull())
      {
        sterm_to_indices[partitions[j].d_sterm].push_back(j);
      }
    }

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
      processPartitions(k, partitions, sti.second, active_indices);
    }
  }
  // initially set substituted term to node
  p.d_sterm = node;
  // for all active indices
  vector<Node> all_vars;
  std::map<TypeNode, unsigned> type_index;
  std::vector<Node> schildren;
  if (!isAssocComm)
  {
    Assert(active_indices.size() == children.size());
    // order matters, and there is no chance we merged children
    schildren.resize(children.size());
  }
  std::vector<Partition> active_partitions;
  for (const unsigned& i : active_indices)
  {
    Trace("sym-dt-debug") << "Reconstruct partition for active index : " << i
                          << std::endl;
    Partition& pa = partitions[i];
    // ensure the variables of pa are fresh
    std::vector<Node> f_vars;
    std::vector<Node> f_subs;
    // add to overall list of variables
    for (const pair<const Node, vector<Node> >& pas : pa.d_subvar_to_vars)
    {
      Node v = pas.first;
      Trace("sym-dt-debug")
          << "...process " << v << " -> " << pas.second << std::endl;
      Assert(!v.isNull());
      TypeNode tnv = v.getType();
      // ensure we use a new index for this variable
      Node new_v = getSymBreakVariableInc(tnv, type_index);
      f_vars.push_back(v);
      f_subs.push_back(new_v);
      // add all vars to partition trie classifier
      for (const Node& c : pas.second)
      {
        if (std::find(all_vars.begin(), all_vars.end(), c) == all_vars.end())
        {
          all_vars.push_back(c);
        }
      }
      for (const Node& x : pas.second)
      {
        Assert(x.getType() == new_v.getType());
        pa.d_var_to_subvar[x] = new_v;
        Trace("sym-dt-debug")
            << "...set var to svar: " << x << " -> " << new_v << std::endl;
      }
    }
    // reconstruct the partition
    for (unsigned j = 0, size = f_vars.size(); j < size; j++)
    {
      Node v = f_vars[j];
      Node new_v = f_subs[j];
      if (new_v != v)
      {
        pa.d_subvar_to_vars[new_v].insert(pa.d_subvar_to_vars[new_v].end(),
                                          pa.d_subvar_to_vars[v].begin(),
                                          pa.d_subvar_to_vars[v].end());
        pa.d_subvar_to_vars.erase(v);
      }
    }
    Assert(f_vars.size() == f_subs.size());
    Assert(!pa.d_sterm.isNull());
    pa.d_sterm = pa.d_sterm.substitute(
        f_vars.begin(), f_vars.end(), f_subs.begin(), f_subs.end());
    if (isAssocComm)
    {
      Assert(!pa.d_sterm.isNull());
      schildren.push_back(pa.d_sterm);
    }
    else
    {
      Assert(i < schildren.size());
      schildren[i] = pa.d_sterm;
    }
    Trace("sym-dt-debug") << "...got : " << pa.d_sterm << std::endl;
    active_partitions.push_back(pa);
  }

  PartitionTrie pt;
  std::map<Node, Node> var_to_svar;
  type_index.clear();
  // Build the partition trie
  std::sort(all_vars.begin(), all_vars.end());
  for (const Node& n : all_vars)
  {
    Node an = pt.addNode(n, active_partitions);
    // if this is a new node, allocate
    if (an == n)
    {
      Node new_v = getSymBreakVariableInc(n.getType(), type_index);
      var_to_svar[n] = new_v;
    }
  }

  // Get the new partition
  pt.getNewPartition(p, pt, var_to_svar);

  // Reconstruct the node
  p.d_term = node;
  Assert(!p.d_sterm.isNull());
  Trace("sym-dt-debug") << "[sym-dt] Reconstructing node: " << node
                        << ", #children = " << schildren.size() << "/"
                        << children.size() << endl;
  if (isAssocComm)
  {
    p.d_sterm = mkAssociativeNode(k, schildren);
  }
  else
  {
    if (node.getMetaKind() == kind::metakind::PARAMETERIZED)
    {
      schildren.insert(schildren.begin(), node.getOperator());
    }
    p.d_sterm = nm->mkNode(k, schildren);
  }
  Trace("sym-dt-debug") << "...return sterm: " << p.d_sterm << std::endl;
  Trace("sym-dt-debug") << ".....types: " << p.d_sterm.getType() << " "
                        << node.getType() << std::endl;
  Assert(p.d_sterm.getType() == node.getType());

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

/** A basic trie for storing vectors of arguments */
class NodeTrie
{
 public:
  NodeTrie() : d_value(-1) {}
  /** value of this node, -1 if unset */
  int d_value;
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
      if (d_value == -1)
      {
        d_value = static_cast<int>(value);
      }
      return d_value;
    }
    return d_children[args[index]].add(value, args, index + 1);
  }
};

void SymmetryDetect::processPartitions(
    Kind k,
    std::vector<Partition>& partitions,
    const std::vector<unsigned>& indices,
    std::unordered_set<unsigned>& active_indices)
{
  Assert(!indices.empty());
  unsigned first_index = indices[0];

  unsigned num_sb_vars = partitions[first_index].d_subvar_to_vars.size();
  if (num_sb_vars != 1)
  {
    // can only handle symmetries that are classified by { n }
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
    Trace("sym-dt-debug") << "Merge..." << std::endl;
    // now, try to merge these partitions
    mergePartitions(k, partitions, check_indices, active_indices);
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
    Trace("sym-dt-debug") << "  merge indices ";
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

  // TODO (#2198): process indices for distinct types separately
  for (unsigned index : indices)
  {
    if (pm.merge(partitions, index, active_indices))
    {
      Trace("sym-dt-debug") << "    ......we merged, recurse" << std::endl;
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

}  // namespace symbreak
}  // namespace passes
}  // namespace preprocessing
}  // namespace CVC4
