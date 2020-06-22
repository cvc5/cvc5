/*********************                                                        */
/*! \file inst_match_trie.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Morgan Deters, Tim King
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Implementation of inst match class
 **/

#include "theory/quantifiers/inst_match_trie.h"

#include "theory/quantifiers/instantiate.h"
#include "theory/quantifiers/quant_util.h"
#include "theory/quantifiers/term_database.h"
#include "theory/quantifiers_engine.h"

using namespace CVC4::context;

namespace CVC4 {
namespace theory {
namespace inst {

bool InstMatchTrie::addInstMatch(QuantifiersEngine* qe,
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
        it->second.addInstMatch(qe, f, m, modEq, imtio, onlyExist, index + 1);
    if (!onlyExist || !ret)
    {
      return ret;
    }
  }
  if (modEq)
  {
    // check modulo equality if any other instantiation match exists
    if (!n.isNull() && qe->getEqualityQuery()->getEngine()->hasTerm(n))
    {
      eq::EqClassIterator eqc(
          qe->getEqualityQuery()->getEngine()->getRepresentative(n),
          qe->getEqualityQuery()->getEngine());
      while (!eqc.isFinished())
      {
        Node en = (*eqc);
        if (en != n)
        {
          std::map<Node, InstMatchTrie>::iterator itc = d_data.find(en);
          if (itc != d_data.end())
          {
            if (itc->second.addInstMatch(
                    qe, f, m, modEq, imtio, true, index + 1))
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
    d_data[n].addInstMatch(qe, f, m, modEq, imtio, false, index + 1);
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

bool InstMatchTrie::recordInstLemma(Node q,
                                    std::vector<Node>& m,
                                    Node lem,
                                    ImtIndexOrder* imtio,
                                    unsigned index)
{
  if (index == q[0].getNumChildren()
      || (imtio && index == imtio->d_order.size()))
  {
    setInstLemma(lem);
    return true;
  }
  unsigned i_index = imtio ? imtio->d_order[index] : index;
  std::map<Node, InstMatchTrie>::iterator it = d_data.find(m[i_index]);
  if (it != d_data.end())
  {
    return it->second.recordInstLemma(q, m, lem, imtio, index + 1);
  }
  return false;
}

void InstMatchTrie::print(std::ostream& out,
                          Node q,
                          std::vector<TNode>& terms,
                          bool& firstTime,
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
      if (firstTime)
      {
        out << "(instantiation " << q << std::endl;
        firstTime = false;
      }
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
      d.second.print(out, q, terms, firstTime, useActive, active);
      terms.pop_back();
    }
  }
}

void InstMatchTrie::getInstantiations(std::vector<Node>& insts,
                                      Node q,
                                      std::vector<Node>& terms,
                                      QuantifiersEngine* qe,
                                      bool useActive,
                                      std::vector<Node>& active) const
{
  if (terms.size() == q[0].getNumChildren())
  {
    if (useActive)
    {
      if (hasInstLemma())
      {
        Node lem = getInstLemma();
        if (std::find(active.begin(), active.end(), lem) != active.end())
        {
          insts.push_back(lem);
        }
      }
    }
    else
    {
      if (hasInstLemma())
      {
        insts.push_back(getInstLemma());
      }
      else if (!options::trackInstLemmas())
      {
        // If we are tracking instantiation lemmas, then hasInstLemma()
        // corresponds exactly to when the lemma was successfully added.
        // Hence the above condition guards the case where the instantiation
        // was recorded but not sent out as a lemma.
        insts.push_back(qe->getInstantiate()->getInstantiation(q, terms, true));
      }
    }
  }
  else
  {
    for (const std::pair<const Node, InstMatchTrie>& d : d_data)
    {
      terms.push_back(d.first);
      d.second.getInstantiations(insts, q, terms, qe, useActive, active);
      terms.pop_back();
    }
  }
}

void InstMatchTrie::getExplanationForInstLemmas(
    Node q,
    std::vector<Node>& terms,
    const std::vector<Node>& lems,
    std::map<Node, Node>& quant,
    std::map<Node, std::vector<Node> >& tvec) const
{
  if (terms.size() == q[0].getNumChildren())
  {
    if (hasInstLemma())
    {
      Node lem = getInstLemma();
      if (std::find(lems.begin(), lems.end(), lem) != lems.end())
      {
        quant[lem] = q;
        tvec[lem].clear();
        tvec[lem].insert(tvec[lem].end(), terms.begin(), terms.end());
      }
    }
  }
  else
  {
    for (const std::pair<const Node, InstMatchTrie>& d : d_data)
    {
      terms.push_back(d.first);
      d.second.getExplanationForInstLemmas(q, terms, lems, quant, tvec);
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

bool CDInstMatchTrie::addInstMatch(QuantifiersEngine* qe,
                                   Node f,
                                   std::vector<Node>& m,
                                   context::Context* c,
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
    bool ret =
        it->second->addInstMatch(qe, f, m, c, modEq, index + 1, onlyExist);
    if (!onlyExist || !ret)
    {
      return reset || ret;
    }
  }
  if (modEq)
  {
    // check modulo equality if any other instantiation match exists
    if (!n.isNull() && qe->getEqualityQuery()->getEngine()->hasTerm(n))
    {
      eq::EqClassIterator eqc(
          qe->getEqualityQuery()->getEngine()->getRepresentative(n),
          qe->getEqualityQuery()->getEngine());
      while (!eqc.isFinished())
      {
        Node en = (*eqc);
        if (en != n)
        {
          std::map<Node, CDInstMatchTrie*>::iterator itc = d_data.find(en);
          if (itc != d_data.end())
          {
            if (itc->second->addInstMatch(qe, f, m, c, modEq, index + 1, true))
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
    // std::map< Node, CDInstMatchTrie* >::iterator it = d_data.find( n );
    CDInstMatchTrie* imt = new CDInstMatchTrie(c);
    Assert(d_data.find(n) == d_data.end());
    d_data[n] = imt;
    imt->addInstMatch(qe, f, m, c, modEq, index + 1, false);
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

bool CDInstMatchTrie::recordInstLemma(Node q,
                                      std::vector<Node>& m,
                                      Node lem,
                                      unsigned index)
{
  if (index == q[0].getNumChildren())
  {
    if (d_valid.get())
    {
      setInstLemma(lem);
      return true;
    }
    return false;
  }
  std::map<Node, CDInstMatchTrie*>::iterator it = d_data.find(m[index]);
  if (it != d_data.end())
  {
    return it->second->recordInstLemma(q, m, lem, index + 1);
  }
  return false;
}

void CDInstMatchTrie::print(std::ostream& out,
                            Node q,
                            std::vector<TNode>& terms,
                            bool& firstTime,
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
        if (firstTime)
        {
          out << "(instantiation " << q << std::endl;
          firstTime = false;
        }
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
        d.second->print(out, q, terms, firstTime, useActive, active);
        terms.pop_back();
      }
    }
  }
}

void CDInstMatchTrie::getInstantiations(std::vector<Node>& insts,
                                        Node q,
                                        std::vector<Node>& terms,
                                        QuantifiersEngine* qe,
                                        bool useActive,
                                        std::vector<Node>& active) const
{
  if (d_valid.get())
  {
    if (terms.size() == q[0].getNumChildren())
    {
      if (useActive)
      {
        if (hasInstLemma())
        {
          Node lem = getInstLemma();
          if (std::find(active.begin(), active.end(), lem) != active.end())
          {
            insts.push_back(lem);
          }
        }
      }
      else
      {
        if (hasInstLemma())
        {
          insts.push_back(getInstLemma());
        }
        else if (!options::trackInstLemmas())
        {
          // Like in the context-independent case, hasInstLemma()
          // corresponds exactly to when the lemma was successfully added when
          // trackInstLemmas() is true.
          insts.push_back(
              qe->getInstantiate()->getInstantiation(q, terms, true));
        }
      }
    }
    else
    {
      for (const std::pair<const Node, CDInstMatchTrie*>& d : d_data)
      {
        terms.push_back(d.first);
        d.second->getInstantiations(insts, q, terms, qe, useActive, active);
        terms.pop_back();
      }
    }
  }
}

void CDInstMatchTrie::getExplanationForInstLemmas(
    Node q,
    std::vector<Node>& terms,
    const std::vector<Node>& lems,
    std::map<Node, Node>& quant,
    std::map<Node, std::vector<Node> >& tvec) const
{
  if (d_valid.get())
  {
    if (terms.size() == q[0].getNumChildren())
    {
      if (hasInstLemma())
      {
        Node lem;
        if (std::find(lems.begin(), lems.end(), lem) != lems.end())
        {
          quant[lem] = q;
          tvec[lem].clear();
          tvec[lem].insert(tvec[lem].end(), terms.begin(), terms.end());
        }
      }
    }
    else
    {
      for (const std::pair<const Node, CDInstMatchTrie*>& d : d_data)
      {
        terms.push_back(d.first);
        d.second->getExplanationForInstLemmas(q, terms, lems, quant, tvec);
        terms.pop_back();
      }
    }
  }
}

} /* CVC4::theory::inst namespace */
} /* CVC4::theory namespace */
} /* CVC4 namespace */
