/*********************                                                        */
/*! \file inst_match_trie.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Morgan Deters, Tim King
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Implementation of inst match class
 **/

#include "theory/quantifiers/inst_match_trie.h"

#include "theory/quantifiers/instantiate.h"
#include "theory/quantifiers/quant_util.h"
#include "theory/quantifiers/quantifiers_state.h"
#include "theory/quantifiers/term_database.h"
#include "theory/quantifiers_engine.h"

using namespace CVC4::context;

namespace CVC4 {
namespace theory {
namespace inst {

bool InstMatchTrie::addInstMatch(quantifiers::QuantifiersState& qs,
                                 Node f,
                                 std::vector<Node>& m,
                                 bool modEq,
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
    bool ret =
        it->second.addInstMatch(qs, f, m, modEq, imtio, onlyExist, index + 1);
    if (!onlyExist || !ret)
    {
      return ret;
    }
  }
  if (modEq)
  {
    // check modulo equality if any other instantiation match exists
    if (!n.isNull() && qs.hasTerm(n))
    {
      eq::EqClassIterator eqc(qs.getRepresentative(n), qs.getEqualityEngine());
      while (!eqc.isFinished())
      {
        Node en = (*eqc);
        if (en != n)
        {
          std::map<Node, InstMatchTrie>::iterator itc = d_data.find(en);
          if (itc != d_data.end())
          {
            if (itc->second.addInstMatch(
                    qs, f, m, modEq, imtio, true, index + 1))
            {
              return false;
            }
          }
        }
        ++eqc;
      }
    }
  }
  if (!onlyExist)
  {
    d_data[n].addInstMatch(qs, f, m, modEq, imtio, false, index + 1);
  }
  return true;
}

bool InstMatchTrie::removeInstMatch(Node q,
                                    std::vector<Node>& m,
                                    ImtIndexOrder* imtio,
                                    unsigned index)
{
  Assert(index < q[0].getNumChildren());
  Assert(!imtio || index < imtio->d_order.size());
  unsigned i_index = imtio ? imtio->d_order[index] : index;
  Node n = m[i_index];
  std::map<Node, InstMatchTrie>::iterator it = d_data.find(n);
  if (it != d_data.end())
  {
    if ((index + 1) == q[0].getNumChildren()
        || (imtio && (index + 1) == imtio->d_order.size()))
    {
      d_data.erase(n);
      return true;
    }
    return it->second.removeInstMatch(q, m, imtio, index + 1);
  }
  return false;
}

void InstMatchTrie::print(std::ostream& out,
                          Node q,
                          std::vector<TNode>& terms,
                          bool useActive,
                          std::vector<Node>& active) const
{
  if (terms.size() == q[0].getNumChildren())
  {
    bool print;
    if (useActive)
    {
      if (hasInstLemma())
      {
        Node lem = getInstLemma();
        print = std::find(active.begin(), active.end(), lem) != active.end();
      }
      else
      {
        print = false;
      }
    }
    else
    {
      print = true;
    }
    if (print)
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
  }
  else
  {
    for (const std::pair<const Node, InstMatchTrie>& d : d_data)
    {
      terms.push_back(d.first);
      d.second.print(out, q, terms, useActive, active);
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

CDInstMatchTrie::~CDInstMatchTrie()
{
  for (std::pair<const Node, CDInstMatchTrie*>& d : d_data)
  {
    CDInstMatchTrie* current = d.second;
    delete current;
  }
  d_data.clear();
}

bool CDInstMatchTrie::addInstMatch(quantifiers::QuantifiersState& qs,
                                   Node f,
                                   std::vector<Node>& m,
                                   bool modEq,
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
    bool ret = it->second->addInstMatch(qs, f, m, modEq, index + 1, onlyExist);
    if (!onlyExist || !ret)
    {
      return reset || ret;
    }
  }
  if (modEq)
  {
    // check modulo equality if any other instantiation match exists
    if (!n.isNull() && qs.hasTerm(n))
    {
      eq::EqClassIterator eqc(qs.getRepresentative(n), qs.getEqualityEngine());
      while (!eqc.isFinished())
      {
        Node en = (*eqc);
        if (en != n)
        {
          std::map<Node, CDInstMatchTrie*>::iterator itc = d_data.find(en);
          if (itc != d_data.end())
          {
            if (itc->second->addInstMatch(qs, f, m, modEq, index + 1, true))
            {
              return false;
            }
          }
        }
        ++eqc;
      }
    }
  }

  if (!onlyExist)
  {
    CDInstMatchTrie* imt = new CDInstMatchTrie(qs.getUserContext());
    Assert(d_data.find(n) == d_data.end());
    d_data[n] = imt;
    imt->addInstMatch(qs, f, m, modEq, index + 1, false);
  }
  return true;
}

bool CDInstMatchTrie::removeInstMatch(Node q,
                                      std::vector<Node>& m,
                                      unsigned index)
{
  if (index == q[0].getNumChildren())
  {
    if (d_valid.get())
    {
      d_valid.set(false);
      return true;
    }
    return false;
  }
  std::map<Node, CDInstMatchTrie*>::iterator it = d_data.find(m[index]);
  if (it != d_data.end())
  {
    return it->second->removeInstMatch(q, m, index + 1);
  }
  return false;
}

void CDInstMatchTrie::print(std::ostream& out,
                            Node q,
                            std::vector<TNode>& terms,
                            bool useActive,
                            std::vector<Node>& active) const
{
  if (d_valid.get())
  {
    if (terms.size() == q[0].getNumChildren())
    {
      bool print;
      if (useActive)
      {
        if (hasInstLemma())
        {
          Node lem = getInstLemma();
          print = std::find(active.begin(), active.end(), lem) != active.end();
        }
        else
        {
          print = false;
        }
      }
      else
      {
        print = true;
      }
      if (print)
      {
        out << "  ( ";
        for (unsigned i = 0; i < terms.size(); i++)
        {
          if (i > 0) out << " ";
          out << terms[i];
        }
        out << " )" << std::endl;
      }
    }
    else
    {
      for (const std::pair<const Node, CDInstMatchTrie*>& d : d_data)
      {
        terms.push_back(d.first);
        d.second->print(out, q, terms, useActive, active);
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

} /* CVC4::theory::inst namespace */
} /* CVC4::theory namespace */
} /* CVC4 namespace */
