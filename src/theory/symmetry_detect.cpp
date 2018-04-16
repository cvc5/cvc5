/*********************                                                        */
/*! \file symmetry_detect.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **  Paul Meng, Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2018 by the authors listed in the file AUTHORS
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

SymmetryDetect::Partition SymmetryDetect::detect(const vector<Node>& assertions)
{
  Partition p =
      findPartitions(NodeManager::currentNM()->mkNode(kind::AND, assertions));
  Trace("sym-dt") << endl
                  << "------------------------------ The Final Partition "
                     "------------------------------"
                  << endl;
  printPartition(p);
  return p;
}

void SymmetryDetect::getPartition(vector<vector<Node> >& parts,
                                  const vector<Node>& assertions)
{
  Partition p = detect(assertions);

  for (map<Node, vector<Node> >::iterator subvar_to_vars_it =
           p.d_subvar_to_vars.begin();
       subvar_to_vars_it != p.d_subvar_to_vars.end();
       ++subvar_to_vars_it)
  {
    parts.push_back(subvar_to_vars_it->second);
  }
}

SymmetryDetect::Partition SymmetryDetect::findPartitions(Node node)
{
  Trace("sym-dt")
      << "------------------------------------------------------------"
      << endl;
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
                  << " with operator " << node.getKind() << endl;
  collectChildren(node, children);
  Trace("sym-dt") << "[sym-dt] children: " << children
                  << endl;

  // Create partitions for children
  for (vector<Node>::iterator children_it = children.begin();
       children_it != children.end();
       ++children_it)
  {
    partitions.push_back(findPartitions(*children_it));
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
  for (unordered_set<Node, NodeHashFunction>::iterator vars_it = vars.begin();
       vars_it != vars.end();
       ++vars_it)
  {
    pt.addNode(*vars_it, partitions);
  }

  // Get the new partition
  pt.getNewPartition(p, pt);

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

  // Collect singleton partitions: subvar_to_expr, subvar_to_var, and variables
  for (vector<Partition>::iterator part_it = partitions.begin();
       part_it != partitions.end();
       ++part_it)
  {
    if ((*part_it).d_var_to_subvar.size() == 1)
    {
      vars.insert(((*part_it).d_var_to_subvar.begin())->first);
      subvar_to_expr[((*part_it).d_var_to_subvar.begin())->second] =
          (*part_it).d_term;
      subvar_to_var[((*part_it).d_var_to_subvar.begin())->second] =
          ((*part_it).d_var_to_subvar.begin())->first;
    }
    else if ((*part_it).d_var_to_subvar.size() >= 2)
    {
      for (pair<const Node, Node>& var_to_subvar : (*part_it).d_var_to_subvar)
      {
        vars.insert(var_to_subvar.first);
      }
      // Only add partitions that have more than 1 variable
      new_partitions.push_back(*part_it);
    }
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
  Kind k = node.getKind();

  if(!theory::quantifiers::TermUtil::isAssoc(k))
  {
    children.insert(children.end(), node.begin(), node.end());
    return;
  }

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
      if (cur.getKind() == k)
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

void SymmetryDetect::PartitionTrie::getNewPartition(Partition& part,
                                                    PartitionTrie& pt)
{
  if (!pt.d_variables.empty())
  {
    vector<Node> vars;
    Node fresh_var = NodeManager::currentNM()->mkSkolem(
        "sym_bk", pt.d_variables[0].getType());
    Trace("sym-dt")
        << "[sym-dt] A partition from leaves of the partition trie:{";

    for (vector<Node>::iterator var_it = pt.d_variables.begin();
         var_it != pt.d_variables.end();
         ++var_it)
    {
      Trace("sym-dt") << " " << *var_it;
      vars.push_back(*var_it);
      part.d_var_to_subvar[*var_it] = fresh_var;
    }
    Trace("sym-dt") << " }" << endl;
    part.d_subvar_to_vars[fresh_var] = vars;
  }
  else
  {
    for (map<Node, PartitionTrie>::iterator part_it = pt.d_children.begin();
         part_it != pt.d_children.end();
         ++part_it)
    {
      getNewPartition(part, part_it->second);
    }
  }
}

void SymmetryDetect::getVariables(vector<Partition>& partitions,
                                  unordered_set<Node, NodeHashFunction>& vars)
{
  for (vector<Partition>::iterator part_it = partitions.begin();
       part_it != partitions.end();
       ++part_it)
  {
    for (map<Node, vector<Node> >::iterator sub_var_it =
             (*part_it).d_subvar_to_vars.begin();
         sub_var_it != (*part_it).d_subvar_to_vars.end();
         ++sub_var_it)
    {
      vars.insert((sub_var_it->second).begin(), (sub_var_it->second).end());
    }
  }
}

void SymmetryDetect::PartitionTrie::addNode(Node target_var,
                                            vector<Partition>& partitions)
{
  Trace("sym-dt") << "[sym-dt] Add a variable {" << target_var
                  << "} to the partition trie..." << endl;
  vector<Node> subvars;

  for (vector<Partition>::iterator part_it = partitions.begin();
       part_it != partitions.end();
       ++part_it)
  {
    map<Node, Node>::iterator var_sub_it =
        (*part_it).d_var_to_subvar.find(target_var);

    if (var_sub_it != (*part_it).d_var_to_subvar.end())
    {
      for (map<Node, vector<Node> >::iterator sub_vars_it =
               (*part_it).d_subvar_to_vars.begin();
           sub_vars_it != (*part_it).d_subvar_to_vars.end();
           ++sub_vars_it)
      {
        if (var_sub_it->second == sub_vars_it->first)
        {
          subvars.push_back(var_sub_it->second);
        }
        else
        {
          subvars.push_back(Node::null());
        }
      }
    }
    else
    {
      subvars.resize(subvars.size()+(*part_it).d_subvar_to_vars.size());
    }
  }

  Trace("sym-dt") << "[sym-dt] Substitution variables for the variable "
                  << target_var << ": " << subvars << endl;
  addNode(target_var, subvars);
}

void SymmetryDetect::PartitionTrie::addNode(Node target_var,
                                            vector<Node>& subvars)
{
  if (subvars.empty())
  {
    d_variables.push_back(target_var);
  }
  else
  {
    vector<Node> new_subs;
    map<Node, PartitionTrie>::iterator children_it =
        d_children.find(subvars[0]);

    if (subvars.begin() + 1 < subvars.end())
    {
      new_subs.insert(new_subs.begin(), subvars.begin() + 1, subvars.end());
    }
    if (children_it != d_children.end())
    {
      (children_it->second).addNode(target_var, new_subs);
    }
    else
    {
      PartitionTrie pt;

      pt.addNode(target_var, new_subs);
      d_children[subvars[0]] = pt;
    }
  }
}

void SymmetryDetect::printPartition(Partition p)
{
  for (map<Node, vector<Node> >::iterator sub_vars_it =
           p.d_subvar_to_vars.begin();
       sub_vars_it != p.d_subvar_to_vars.end();
       ++sub_vars_it)
  {
    Trace("sym-dt") << "[sym-dt] Partition: " << sub_vars_it->first << " -> {";

    for (vector<Node>::iterator part_it = (sub_vars_it->second).begin();
         part_it != (sub_vars_it->second).end();
         ++part_it)
    {
      Trace("sym-dt") << " " << *part_it;
    }
    Trace("sym-dt") << " }" << endl;
  }
}

}  // namespace CVC4
