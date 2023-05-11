/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Andres Noetzli, Morgan Deters
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Implementation of inst match trie class.
 */

#include "theory/quantifiers/inst_match_trie.h"

using namespace cvc5::context;

namespace cvc5::internal {
namespace theory {
namespace quantifiers {

bool InstMatchTrie::existsInstMatch(Node q,
                                    const std::vector<Node>& m,
                                    ImtIndexOrder* imtio,
                                    unsigned index)
{
  return !addInstMatch(q, m, imtio, true, index);
}

bool InstMatchTrie::addInstMatch(Node f,
                                 const std::vector<Node>& m,
                                 ImtIndexOrder* imtio,
                                 bool onlyExist,
                                 unsigned index)
{
  if (index == f[0].getNumChildren()
      || (imtio && index == imtio->d_order.size()))
  {
    return false;
  }
  unsigned i_index = imtio ? imtio->d_order[index] : index;
  Node n = m[i_index];
  std::map<Node, InstMatchTrie>::iterator it = d_data.find(n);
  if (it != d_data.end())
  {
    bool ret = it->second.addInstMatch(f, m, imtio, onlyExist, index + 1);
    if (!onlyExist || !ret)
    {
      return ret;
    }
  }
  if (!onlyExist)
  {
    d_data[n].addInstMatch(f, m, imtio, false, index + 1);
  }
  return true;
}

void InstMatchTrie::print(std::ostream& out,
                          Node q,
                          std::vector<TNode>& terms) const
{
  if (terms.size() == q[0].getNumChildren())
  {
    out << "  ( ";
    for (unsigned i = 0, size = terms.size(); i < size; i++)
    {
      if (i > 0)
      {
        out << ", ";
      }
      out << terms[i];
    }
    out << " )" << std::endl;
  }
  else
  {
    for (const std::pair<const Node, InstMatchTrie>& d : d_data)
    {
      terms.push_back(d.first);
      d.second.print(out, q, terms);
      terms.pop_back();
    }
  }
}

void InstMatchTrie::getInstantiations(
    Node q, std::vector<std::vector<Node>>& insts) const
{
  std::vector<Node> terms;
  getInstantiations(q, insts, terms);
}

void InstMatchTrie::getInstantiations(Node q,
                                      std::vector<std::vector<Node>>& insts,
                                      std::vector<Node>& terms) const
{
  if (terms.size() == q[0].getNumChildren())
  {
    insts.push_back(terms);
  }
  else
  {
    for (const std::pair<const Node, InstMatchTrie>& d : d_data)
    {
      terms.push_back(d.first);
      d.second.getInstantiations(q, insts, terms);
      terms.pop_back();
    }
  }
}

void InstMatchTrie::clear() { d_data.clear(); }

void InstMatchTrie::print(std::ostream& out, Node q) const
{
  std::vector<TNode> terms;
  print(out, q, terms);
}

CDInstMatchTrie::~CDInstMatchTrie()
{
  for (std::pair<const Node, CDInstMatchTrie*>& d : d_data)
  {
    CDInstMatchTrie* current = d.second;
    delete current;
  }
  d_data.clear();
}

bool CDInstMatchTrie::existsInstMatch(context::Context* context,
                                      Node q,
                                      const std::vector<Node>& m,
                                      unsigned index)
{
  return !addInstMatch(context, q, m, index, true);
}

bool CDInstMatchTrie::addInstMatch(context::Context* context,
                                   Node f,
                                   const std::vector<Node>& m,
                                   unsigned index,
                                   bool onlyExist)
{
  bool reset = false;
  if (!d_valid.get())
  {
    if (onlyExist)
    {
      return true;
    }
    else
    {
      d_valid.set(true);
      reset = true;
    }
  }
  if (index == f[0].getNumChildren())
  {
    return reset;
  }
  Node n = m[index];
  std::map<Node, CDInstMatchTrie*>::iterator it = d_data.find(n);
  if (it != d_data.end())
  {
    bool ret = it->second->addInstMatch(context, f, m, index + 1, onlyExist);
    if (!onlyExist || !ret)
    {
      return reset || ret;
    }
  }
  if (!onlyExist)
  {
    CDInstMatchTrie* imt = new CDInstMatchTrie(context);
    Assert(d_data.find(n) == d_data.end());
    d_data[n] = imt;
    imt->addInstMatch(context, f, m, index + 1, false);
  }
  return true;
}

void CDInstMatchTrie::print(std::ostream& out,
                            Node q,
                            std::vector<TNode>& terms) const
{
  if (d_valid.get())
  {
    if (terms.size() == q[0].getNumChildren())
    {
      out << "  ( ";
      for (unsigned i = 0; i < terms.size(); i++)
      {
        if (i > 0) out << " ";
        out << terms[i];
      }
      out << " )" << std::endl;
    }
    else
    {
      for (const std::pair<const Node, CDInstMatchTrie*>& d : d_data)
      {
        terms.push_back(d.first);
        d.second->print(out, q, terms);
        terms.pop_back();
      }
    }
  }
}

void CDInstMatchTrie::getInstantiations(
    Node q, std::vector<std::vector<Node>>& insts) const
{
  std::vector<Node> terms;
  getInstantiations(q, insts, terms);
}

void CDInstMatchTrie::getInstantiations(Node q,
                                        std::vector<std::vector<Node>>& insts,
                                        std::vector<Node>& terms) const
{
  if (!d_valid.get())
  {
    // do nothing
  }
  else if (terms.size() == q[0].getNumChildren())
  {
    insts.push_back(terms);
  }
  else
  {
    for (const std::pair<const Node, CDInstMatchTrie*>& d : d_data)
    {
      terms.push_back(d.first);
      d.second->getInstantiations(q, insts, terms);
      terms.pop_back();
    }
  }
}

void CDInstMatchTrie::print(std::ostream& out, Node q) const
{
  std::vector<TNode> terms;
  print(out, q, terms);
}

bool InstMatchTrieOrdered::addInstMatch(Node q, const std::vector<Node>& m)
{
  return d_imt.addInstMatch(q, m, d_imtio);
}

bool InstMatchTrieOrdered::existsInstMatch(Node q, const std::vector<Node>& m)
{
  return d_imt.existsInstMatch(q, m, d_imtio);
}

}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal
