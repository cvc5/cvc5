/*********************                                                        */
/*! \file symmetry_detect.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **  Paul Meng, Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2017 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Symmetry detection module
 **/

#include "theory/symmetry_detect.h"
#include "theory/quantifiers/term_util.h"
#include "theory/rewriter.h"

using namespace std;

namespace CVC4 {

SymmetryDetect::Partition SymmetryDetect::detect(vector<Node>& assertions)
{
  Node node = d_trueNode;
  vector<Node>::iterator assertions_it = assertions.begin();

  while (assertions_it != assertions.end())
  {
    node = NodeManager::currentNM()->mkNode(kind::AND, node, *assertions_it);
    ++assertions_it;
  }

  Partition p = findPartitions(node);
  Trace("sym-dt") << endl
                  << "------------------------------ The Final Partition "
                     "------------------------------"
                  << std::endl;
  printPartition(p);
  return p;
}

void SymmetryDetect::getPartition(vector<vector<Node> >& parts,
                                  vector<Node>& assertions)
{
  Partition p = detect(assertions);
  map<Node, vector<Node> >::iterator subvar_to_vars_it =
      p.d_subvar_to_vars.begin();

  while (subvar_to_vars_it != p.d_subvar_to_vars.end())
  {
    parts.push_back(subvar_to_vars_it->second);
    ++subvar_to_vars_it;
  }
}

SymmetryDetect::Partition SymmetryDetect::findPartitions(Node node)
{
  Trace("sym-dt")
      << "------------------------------------------------------------"
      << std::endl;
  Trace("sym-dt") << "[sym-dt] findPartitions gets a term: " << node << endl;
  map<Node, Partition>::iterator partition = d_term_partition.find(node);

  // Return its partition from cache if we have processed the node before
  if (partition != d_term_partition.end())
  {
    Trace("sym-dt") << "[sym-dt] We have seen the node " << node
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
    Node fresh_var = NodeManager::currentNM()->mkSkolem("sym_bk", type);

    vars.push_back(node);
    p.d_term = node;
    p.d_subvar_to_vars[fresh_var] = vars;
    p.d_var_to_subvar[node] = fresh_var;
    d_term_partition[node] = p;
    return p;
  }
  // If node is a constant
  else if (node.isConst())
  {
    p.d_term = node;
    d_term_partition[node] = p;
    return p;
  }

  // Children of node
  vector<Node> children;
  // Partitions of children
  vector<Partition> partitions;

  // Get all children of node
  Trace("sym-dt") << "[sym-dt] collectChildren for: " << node
                  << " with operator " << node.getKind() << std::endl;
  collectChildren(node, children);
  Trace("sym-dt") << "[sym-dt] children: " << printNodeVector(children)
                  << std::endl;

  // Create partitions for children
  vector<Node>::iterator children_it = children.begin();
  while (children_it != children.end())
  {
    partitions.push_back(findPartitions(*children_it));
    ++children_it;
  }

  Trace("sym-dt") << "----------------------------- Start processing "
                     "partitions -------------------------------"
                  << endl;

  PartitionTrie pt;
  unordered_set<Node, NodeHashFunction> vars;

  if (theory::quantifiers::TermUtil::isComm(node.getKind()))
  {
    // Start processing the singleton partitions and collect variables
    processSingletonPartitions(partitions, vars);
  }
  else
  {
    // Get all the variables from the partitions
    getVariables(partitions, vars);
  }

  // Build the partition trie
  unordered_set<Node, NodeHashFunction>::iterator vars_it = vars.begin();
  while (vars_it != vars.end())
  {
    pt.addNode(*vars_it, partitions);
    ++vars_it;
  }

  // Get the new partition
  pt.getNewPartition(p);

  // Reconstruct the node
  Trace("sym-dt") << "[sym-dt] Reconstructing node: " << node << endl;
  p.d_term = node;
  d_term_partition[node] = p;
  printPartition(p);
  return p;
}

void SymmetryDetect::matches(vector<Partition>& partitions,
                             map<Node, Node>& subvar_to_var,
                             map<Node, Node>& subvar_to_expr)
{
  Trace("sym-dt")
      << "[sym-dt] Start testing if singleton partitions can be merged!"
      << endl;

  if (!subvar_to_expr.empty())
  {
    // Replacement variables
    vector<Node> repls;
    // Variables that have been merged
    unordered_set<Node, NodeHashFunction> merged;
    // Put the variable in repls
    repls.push_back((subvar_to_expr.begin())->first);

    for (map<Node, Node>::iterator expr_it1 = subvar_to_expr.begin();
         expr_it1 != subvar_to_expr.end();
         ++expr_it1)
    {
      // Skip expr_it1->first, if it has been merged
      if (merged.find(expr_it1->first) != merged.end())
      {
        continue;
      }

      Partition p;
      vector<Node> subs;
      vector<Node> part;
      Node fst_var = subvar_to_var.find(expr_it1->first)->second;

      part.push_back(fst_var);
      subs.push_back(fst_var);
      merged.insert(expr_it1->first);
      p.d_var_to_subvar[fst_var] = expr_it1->first;
      Node sub_expr1 =
          (expr_it1->second)
              .substitute(subs.begin(), subs.end(), repls.begin(), repls.end());

      for (map<Node, Node>::iterator expr_it2 = subvar_to_expr.begin();
           expr_it2 != subvar_to_expr.end();
           ++expr_it2)
      {
        if (merged.find(expr_it2->first) != merged.end())
        {
          continue;
        }
        if ((expr_it1->second).getType() != (expr_it2->second).getType())
        {
          continue;
        }
        vector<Node> subs2;
        Node snd_var = subvar_to_var.find(expr_it2->first)->second;

        subs2.push_back(snd_var);
        Node sub_expr2 =
            (expr_it2->second)
                .substitute(
                    subs2.begin(), subs2.end(), repls.begin(), repls.end());
        Trace("sym-dt") << "[sym-dt] Testing if " << sub_expr1
                        << " is equivalent to " << sub_expr2 << endl;

        if (sub_expr1 == sub_expr2)
        {
          Trace("sym-dt") << "[sym-dt] Merge variable " << fst_var
                          << " with variable " << snd_var << endl;
          merged.insert(expr_it2->first);
          part.push_back(snd_var);
          p.d_var_to_subvar[snd_var] = expr_it1->first;
        }
      }
      p.d_subvar_to_vars[expr_it1->first] = part;
      Trace("sym-dt") << "[sym-dt] Add a new partition after merging: " << endl;
      printPartition(p);
      partitions.push_back(p);
    }
  }
}

void SymmetryDetect::processSingletonPartitions(
    vector<Partition>& partitions, unordered_set<Node, NodeHashFunction>& vars)
{
  Trace("sym-dt") << "[sym-dt] Start post-processing partitions with size = "
                  << partitions.size() << endl;

  // Mapping between the substitution variable to the actual variable
  map<Node, Node> subvar_to_var;
  // Mapping between the substitution variable to the actual expression
  map<Node, Node> subvar_to_expr;
  // Partitions that have 2 or more variables
  vector<Partition> new_partitions;
  vector<Partition>::iterator part_it = partitions.begin();

  // Collect singleton partitions: subvar_to_expr, subvar_to_var, and variables
  while (part_it != partitions.end())
  {
    if (!(*part_it).d_var_to_subvar.empty()
        && (*part_it).d_var_to_subvar.size() == 1)
    {
      vars.insert(((*part_it).d_var_to_subvar.begin())->first);
      subvar_to_expr[((*part_it).d_var_to_subvar.begin())->second] =
          (*part_it).d_term;
      subvar_to_var[((*part_it).d_var_to_subvar.begin())->second] =
          ((*part_it).d_var_to_subvar.begin())->first;
    }
    else if (!(*part_it).d_var_to_subvar.empty()
             && (*part_it).d_var_to_subvar.size() >= 2)
    {
      map<Node, Node>::iterator var_to_subvar_it =
          (*part_it).d_var_to_subvar.begin();

      while (var_to_subvar_it != (*part_it).d_var_to_subvar.end())
      {
        vars.insert(var_to_subvar_it->first);
        ++var_to_subvar_it;
      }
      // Only add partitions that have more than 1 variable
      new_partitions.push_back(*part_it);
    }
    ++part_it;
  }

  // Save all partitions that have more than 1 variable
  partitions = new_partitions;

  // Do matches on singleton terms
  if (!subvar_to_var.empty())
  {
    matches(partitions, subvar_to_var, subvar_to_expr);
  }
}

void SymmetryDetect::collectChildren(Node node, vector<Node>& children)
{
  if (theory::quantifiers::TermUtil::isAssoc(node.getKind()))
  {
    // for(const Node& n : node)
    for (unsigned int i = 0; i < node.getNumChildren(); ++i)
    {
      collectChildren(node[i], node.getKind(), children);
    }
  }
  else
  {
    for (unsigned int i = 0; i < node.getNumChildren(); ++i)
    {
      children.push_back(node[i]);
    }
  }
}

void SymmetryDetect::collectChildren(Node node, Kind k, vector<Node>& children)
{
  if (node.getKind() == k)
  {
    for (unsigned int i = 0; i < node.getNumChildren(); ++i)
    {
      collectChildren(node[i], k, children);
    }
  }
  else
  {
    children.push_back(node);
  }
}

string SymmetryDetect::printNodeVector(vector<Node> nodes)
{
  string result;
  vector<Node>::iterator node_it = nodes.begin();

  while (node_it != nodes.end())
  {
    result += " " + (*node_it).toString();
    ++node_it;
    if (node_it != nodes.end())
    {
      result += ",";
    }
  }
  result += " ";
  return result;
}

string SymmetryDetect::printNodeSet(unordered_set<Node, NodeHashFunction> nodes)
{
  string result;
  unordered_set<Node, NodeHashFunction>::iterator node_it = nodes.begin();

  while (node_it != nodes.end())
  {
    result += " " + (*node_it).toString();
    ++node_it;
    if (node_it != nodes.end())
    {
      result += ",";
    }
  }
  result += " ";
  return result;
}

void SymmetryDetect::PartitionTrie::getNewPartition(Partition& part)
{
  Trace("sym-dt") << "[sym-dt] Getting the new partitions from the leaves of "
                     "the partition trie:"
                  << std::endl;
  if (!d_variables.empty())
  {
    vector<Node> vars;
    vector<Node>::iterator var_it = d_variables.begin();
    Node fresh_var =
        NodeManager::currentNM()->mkSkolem("sym_bk", d_variables[0].getType());

    while (var_it != d_variables.end())
    {
      vars.push_back(*var_it);
      part.d_var_to_subvar[*var_it] = fresh_var;
      ++var_it;
    }
    part.d_subvar_to_vars[fresh_var] = vars;
  }
  else
  {
    map<Node, PartitionTrie>::iterator part_it = d_children.begin();

    while (part_it != d_children.end())
    {
      getNewPartition(part, part_it->second);
      ++part_it;
    }
  }
}

void SymmetryDetect::PartitionTrie::getNewPartition(Partition& part,
                                                    PartitionTrie& pt)
{
  if (!pt.d_variables.empty())
  {
    vector<Node> vars;
    vector<Node>::iterator var_it = pt.d_variables.begin();
    Node fresh_var = NodeManager::currentNM()->mkSkolem(
        "sym_bk", pt.d_variables[0].getType());
    Trace("sym-dt")
        << "[sym-dt] A partition from leaves of the partition trie:{";

    while (var_it != pt.d_variables.end())
    {
      Trace("sym-dt") << " " << *var_it;
      vars.push_back(*var_it);
      part.d_var_to_subvar[*var_it] = fresh_var;
      ++var_it;
    }
    Trace("sym-dt") << " }" << endl;
    part.d_subvar_to_vars[fresh_var] = vars;
  }
  else
  {
    map<Node, PartitionTrie>::iterator part_it = pt.d_children.begin();
    while (part_it != pt.d_children.end())
    {
      getNewPartition(part, part_it->second);
      ++part_it;
    }
  }
}

void SymmetryDetect::getVariables(vector<Partition>& partitions,
                                  unordered_set<Node, NodeHashFunction>& vars)
{
  vector<Partition>::iterator part_it = partitions.begin();

  while (part_it != partitions.end())
  {
    map<Node, vector<Node> >::iterator sub_var_it =
        (*part_it).d_subvar_to_vars.begin();

    while (sub_var_it != (*part_it).d_subvar_to_vars.end())
    {
      vector<Node>::iterator v_it = (sub_var_it->second).begin();

      while (v_it != (sub_var_it->second).end())
      {
        vars.insert(*v_it);
        ++v_it;
      }
      ++sub_var_it;
    }
    ++part_it;
  }
}

void SymmetryDetect::PartitionTrie::addNode(Node v,
                                            vector<Partition>& partitions)
{
  Trace("sym-dt") << "[sym-dt] Add a variable {" << v
                  << "} to the partition trie..." << endl;
  vector<Node> subvars;
  vector<Partition>::iterator part_it = partitions.begin();

  while (part_it != partitions.end())
  {
    map<Node, Node>::iterator var_sub_it = (*part_it).d_var_to_subvar.find(v);

    if (var_sub_it != (*part_it).d_var_to_subvar.end())
    {
      map<Node, vector<Node> >::iterator sub_vars_it =
          (*part_it).d_subvar_to_vars.begin();

      while (sub_vars_it != (*part_it).d_subvar_to_vars.end())
      {
        if (var_sub_it->second == sub_vars_it->first)
        {
          subvars.push_back(var_sub_it->second);
        }
        else
        {
          subvars.push_back(Node::null());
        }
        ++sub_vars_it;
      }
    }
    else
    {
      map<Node, vector<Node> >::iterator sub_vars_it =
          (*part_it).d_subvar_to_vars.begin();

      while (sub_vars_it != (*part_it).d_subvar_to_vars.end())
      {
        subvars.push_back(Node::null());
        ++sub_vars_it;
      }
    }
    ++part_it;
  }

  Trace("sym-dt") << "[sym-dt] Substitution variables for the variable " << v
                  << ": " << SymmetryDetect::printNodeVector(subvars) << endl;

  if (subvars.size() >= 1)
  {
    map<Node, PartitionTrie>::iterator children_it =
        d_children.find(subvars[0]);

    if (children_it != d_children.end())
    {
      vector<Node> new_subs;
      if (subvars.begin() + 1 < subvars.end())
      {
        new_subs.insert(new_subs.begin(), subvars.begin() + 1, subvars.end());
      }
      (children_it->second).addNode(v, new_subs);
    }
    else
    {
      PartitionTrie pt;
      vector<Node> new_subs;

      if (subvars.begin() + 1 < subvars.end())
      {
        new_subs.insert(new_subs.begin(), subvars.begin() + 1, subvars.end());
      }
      pt.addNode(v, new_subs);
      d_children[subvars[0]] = pt;
    }
  }
}

void SymmetryDetect::PartitionTrie::addNode(Node v, vector<Node>& subs)
{
  if (subs.empty())
  {
    d_variables.push_back(v);
  }
  else
  {
    map<Node, PartitionTrie>::iterator children_it = d_children.find(subs[0]);

    if (children_it != d_children.end())
    {
      vector<Node> new_subs;
      if (subs.begin() + 1 < subs.end())
      {
        new_subs.insert(new_subs.begin(), subs.begin() + 1, subs.end());
      }
      (children_it->second).addNode(v, new_subs);
    }
    else
    {
      PartitionTrie pt;
      vector<Node> new_subs;

      if (subs.begin() + 1 < subs.end())
      {
        new_subs.insert(new_subs.begin(), subs.begin() + 1, subs.end());
      }
      pt.addNode(v, new_subs);
      d_children[subs[0]] = pt;
    }
  }
}

void SymmetryDetect::printPartition(Partition p)
{
  map<Node, vector<Node> >::iterator sub_vars_it = p.d_subvar_to_vars.begin();

  while (sub_vars_it != p.d_subvar_to_vars.end())
  {
    Trace("sym-dt") << "[sym-dt] Partition: " << sub_vars_it->first << " -> {";
    vector<Node>::iterator part_it = (sub_vars_it->second).begin();

    while (part_it != (sub_vars_it->second).end())
    {
      Trace("sym-dt") << " " << *part_it;
      ++part_it;
    }
    Trace("sym-dt") << " }" << endl;
    ++sub_vars_it;
  }
}

}  // namespace CVC4
