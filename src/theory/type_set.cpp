/*********************                                                        */
/*! \file type_set.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Clark Barrett
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Implementation of type set class
 **/
#include "theory/type_set.h"

using namespace std;
using namespace CVC4::kind;

namespace CVC4 {
namespace theory {

TypeSet::~TypeSet()
{
  iterator it;
  for (it = d_typeSet.begin(); it != d_typeSet.end(); ++it)
  {
    delete (*it).second;
  }
  TypeToTypeEnumMap::iterator it2;
  for (it2 = d_teMap.begin(); it2 != d_teMap.end(); ++it2)
  {
    delete (*it2).second;
  }
}

void TypeSet::setTypeEnumeratorProperties(TypeEnumeratorProperties* tep)
{
  d_tep = tep;
}

void TypeSet::add(TypeNode t, TNode n)
{
  iterator it = d_typeSet.find(t);
  std::set<Node>* s;
  if (it == d_typeSet.end())
  {
    s = new std::set<Node>;
    d_typeSet[t] = s;
  }
  else
  {
    s = (*it).second;
  }
  s->insert(n);
}

std::set<Node>* TypeSet::getSet(TypeNode t) const
{
  const_iterator it = d_typeSet.find(t);
  if (it == d_typeSet.end())
  {
    return NULL;
  }
  return (*it).second;
}

Node TypeSet::nextTypeEnum(TypeNode t, bool useBaseType)
{
  TypeEnumerator* te;
  TypeToTypeEnumMap::iterator it = d_teMap.find(t);
  if (it == d_teMap.end())
  {
    te = new TypeEnumerator(t, d_tep);
    d_teMap[t] = te;
  }
  else
  {
    te = (*it).second;
  }
  if (te->isFinished())
  {
    return Node();
  }

  if (useBaseType)
  {
    t = t.getBaseType();
  }
  iterator itSet = d_typeSet.find(t);
  std::set<Node>* s;
  if (itSet == d_typeSet.end())
  {
    s = new std::set<Node>;
    d_typeSet[t] = s;
  }
  else
  {
    s = (*itSet).second;
  }
  Node n = **te;
  while (s->find(n) != s->end())
  {
    ++(*te);
    if (te->isFinished())
    {
      return Node();
    }
    n = **te;
  }
  s->insert(n);
  // add all subterms of n to this set as well
  // this is necessary for parametric types whose values are constructed from
  // other types to ensure that we do not enumerate subterms of other 
  // previously enumerated values
  std::unordered_set<TNode, TNodeHashFunction> visited;
  addSubTerms(n, visited);
  ++(*te);
  return n;
}

void TypeSet::addSubTerms(TNode n,
                          std::unordered_set<TNode, TNodeHashFunction>& visited,
                          bool topLevel)
{
  if (visited.find(n) == visited.end())
  {
    visited.insert(n);
    if (!topLevel)
    {
      add(n.getType(), n);
    }
    for (unsigned i = 0; i < n.getNumChildren(); i++)
    {
      addSubTerms(n[i], visited, false);
    }
  }
}

} /* namespace CVC4::theory */
} /* namespace CVC4 */
