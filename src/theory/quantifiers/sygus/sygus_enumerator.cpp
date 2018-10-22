/*********************                                                        */
/*! \file sygus_enumerator.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2018 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Implementation of sygus_enumerator
 **/

#include "theory/quantifiers/sygus/sygus_enumerator.h"

using namespace CVC4::kind;

namespace CVC4 {
namespace theory {
namespace quantifiers {

SygusEnumerator::SygusEnumerator(TermDbSygus* tds)
    : d_tds(tds), d_tlEnum(nullptr)
{
}

void SygusEnumerator::initialize(Node e)
{
  d_etype = e.getType();
  d_tlEnum = getMasterEnumForType(d_etype);
}

void SygusEnumerator::addValue(Node v)
{
  // do nothing
}

Node SygusEnumerator::getNext()
{
  if (d_tlEnum->increment())
  {
    return d_tlEnum->getCurrent();
  }
  return Node::null();
}

void SygusEnumerator::initializeTermCache(TypeNode tn)
{
  std::map<TypeNode, TermCache>::iterator itt = d_tcache.find(tn);
  if (itt == d_tcache.end())
  {
    d_tcache[tn].initialize(tn, d_tds);
  }
}

SygusEnumerator::TermCache::TermCache()
    : d_tds(nullptr), d_numConClasses(0), d_sizeEnum(0)
{
}
void SygusEnumerator::TermCache::initialize(TypeNode tn, TermDbSygus* tds)
{
  d_tn = tn;
  d_tds = tds;

  // compute static information about tn

  // constructor class 0 is reserved for nullary operators
  d_ccToCons[0].clear();
  d_ccToTypes[0].clear();

  d_numConClasses = 1;
  const Datatype& dt = tn.getDatatype();
  // get argument types for all constructors
  std::map<unsigned, std::vector<TypeNode> > argTypes;
  for (unsigned i = 0, ncons = dt.getNumConstructors(); i < ncons; i++)
  {
    for (unsigned j = 0, nargs = dt[i].getNumArgs(); j < nargs; j++)
    {
      TypeNode tn = TypeNode::fromType(dt[i].getArgType(j));
      argTypes[i].push_back(tn);
    }
  }
  // assign constructors to constructor classes
  for (unsigned i = 0, ncons = dt.getNumConstructors(); i < ncons; i++)
  {
    if (argTypes[i].empty())
    {
      d_ccToCons[0].push_back(i);
      d_cToCIndices[i].clear();
    }
    else
    {
      // determine which constructor class this goes into: currently trivial
      unsigned cclassi = d_numConClasses;

      // allocate new constructor class
      d_ccToTypes[cclassi].insert(
          d_ccToTypes[cclassi].end(), argTypes[i].begin(), argTypes[i].end());
      d_numConClasses++;

      // add to constructor class
      d_ccToCons[cclassi].push_back(i);
      // map to child indices
      for (unsigned j = 0, nargs = dt[i].getNumArgs(); j < nargs; j++)
      {
        d_cToCIndices[i].push_back(j);
      }
    }
  }
}
unsigned SygusEnumerator::TermCache::getNumConstructorClasses() const
{
  return d_numConClasses;
}
void SygusEnumerator::TermCache::getConstructorClass(
    unsigned i, std::vector<unsigned>& cclass) const
{
  std::map<unsigned, std::vector<unsigned> >::const_iterator it =
      d_ccToCons.find(i);
  Assert(it != d_ccToCons.end());
  cclass.insert(cclass.end(), it->second.begin(), it->second.end());
}
void SygusEnumerator::TermCache::getTypesForConstructorClass(
    unsigned i, std::vector<TypeNode>& types) const
{
  std::map<unsigned, std::vector<TypeNode> >::const_iterator it =
      d_ccToTypes.find(i);
  Assert(it != d_ccToTypes.end());
  types.insert(types.end(), it->second.begin(), it->second.end());
}
void SygusEnumerator::TermCache::getChildIndicesForConstructor(
    unsigned i, std::vector<unsigned>& cindices) const
{
  std::map<unsigned, std::vector<unsigned> >::const_iterator it =
      d_cToCIndices.find(i);
  Assert(it != d_cToCIndices.end());
  cindices.insert(cindices.end(), it->second.begin(), it->second.end());
}

bool SygusEnumerator::TermCache::addTerm(Node n)
{
  Node bn = d_tds->sygusToBuiltin(n);
  bn = d_tds->getExtRewriter()->extendedRewrite(bn);
  // must be unique up to rewriting
  if (d_bterms.find(bn) == d_bterms.end())
  {
    d_terms.push_back(n);
    d_bterms.insert(bn);
    return true;
  }
  return false;
}
void SygusEnumerator::TermCache::pushEnumSizeIndex()
{
  d_lastSizeIndex[d_sizeEnum] = d_terms.size();
  d_sizeEnum++;
}
unsigned SygusEnumerator::TermCache::getEnumSize() const { return d_sizeEnum; }
unsigned SygusEnumerator::TermCache::getIndexForSize(unsigned s) const
{
  if (s == 0)
  {
    return 0;
  }
  std::map<unsigned, unsigned>::const_iterator it = d_lastSizeIndex.find(s - 1);
  Assert(it != d_lastSizeIndex.end());
  return it->second;
}

Node SygusEnumerator::TermCache::getTerm(unsigned index) const
{
  Assert(index < d_terms.size());
  return d_terms[index];
}

SygusEnumerator::TermEnum::TermEnum()
    : d_se(nullptr),
      d_isMaster(false),
      d_currSize(0),
      d_sizeLim(0),
      d_consClassNum(0),
      d_consNum(0),
      d_currChildSize(0),
      d_childrenValid(0),
      d_index(0),
      d_indexNextEnd(0),
      d_master(nullptr)
{
}

bool SygusEnumerator::TermEnum::initialize(SygusEnumerator* se,
                                           TypeNode tn,
                                           unsigned sizeLim,
                                           bool sizeExact)
{
  d_se = se;
  d_tn = tn;
  d_se->initializeTermCache(d_tn);
  d_sizeLim = sizeLim;
  d_isMaster = false;

  // must have pointer to the master
  d_master = d_se->getMasterEnumForType(d_tn);

  SygusEnumerator::TermCache& tc = d_se->d_tcache[d_tn];
  // if the size is exact, we start at the limit
  d_currSize = sizeExact ? sizeLim : 0;
  // initialize the index
  d_index = tc.getIndexForSize(d_currSize);
  // initialize the next end index
  d_indexNextEnd = tc.getIndexForSize(d_currSize + 1);
  // ensure that indexNextEnd is valid (it must be greater than d_index)
  return setNextEndIndex();
}

bool SygusEnumerator::TermEnum::initializeMaster(SygusEnumerator* se,
                                                 TypeNode tn)
{
  d_se = se;
  d_tn = tn;
  d_se->initializeTermCache(d_tn);
  d_sizeLim = 0;
  d_isMaster = true;

  d_currSize = 0;
  // we will start with constructor class zero
  d_consClassNum = 0;
  d_ccCons.clear();
  return increment();
}

Node SygusEnumerator::TermEnum::getCurrent()
{
  if (!d_currTerm.isNull())
  {
    return d_currTerm;
  }
  SygusEnumerator::TermCache& tc = d_se->d_tcache[d_tn];
  if (!d_isMaster)
  {
    // lookup in the cache
    return tc.getTerm(d_index);
  }
  // construct based on the children
  std::vector<Node> children;
  const Datatype& dt = d_tn.getDatatype();
  Assert(d_consNum > 0 && d_consNum <= d_ccCons.size());
  // get the current constructor number
  unsigned cnum = d_ccCons[d_consNum - 1];
  children.push_back(Node::fromExpr(dt[cnum].getConstructor()));
  // get indices for this constructor
  std::vector<unsigned> cindices;
  tc.getChildIndicesForConstructor(cnum, cindices);
  // add the current of each child to children
  for (unsigned i : cindices)
  {
    Assert(d_children.find(i) != d_children.end());
    children.push_back(d_children[i].getCurrent());
  }
  return NodeManager::currentNM()->mkNode(APPLY_CONSTRUCTOR, children);
}

unsigned SygusEnumerator::TermEnum::getCurrentSize() { return d_currSize; }

bool SygusEnumerator::TermEnum::increment()
{
  if (!d_isMaster)
  {
    // increment index
    d_index++;
    // ensure that size and the next end index are valid
    return setNextEndIndex();
  }

  SygusEnumerator::TermCache& tc = d_se->d_tcache[d_tn];

  // the maximum index of a constructor class to consider
  unsigned ncc = d_sizeLim == 0 ? 1 : tc.getNumConstructorClasses();

  // have we initialized the current constructor class?
  while (d_ccCons.empty() && d_consClassNum < ncc)
  {
    // get the list of constructors in the constructor class
    tc.getConstructorClass(d_consClassNum, d_ccCons);
    // if there are any...
    if (!d_ccCons.empty())
    {
      // successfully initialized the constructor class
      d_consNum = 0;
      // we will populate the children
      Assert(d_children.empty());
      Assert(d_ccTypes.empty());
      tc.getTypesForConstructorClass(d_consClassNum, d_ccTypes);
      d_currChildSize = 0;
      d_childrenValid = 0;
      // initialize the children into their initial state
      if (!initializeChildren())
      {
        // didn't work (due to size), we will try the next class
        d_ccCons.clear();
        d_ccTypes.clear();
      }
    }
    // increment the next constructor class we will try
    d_consClassNum++;
  }

  // have we run out of constructor classes for this size?
  if (d_ccCons.empty())
  {
    // increment the size bound
    d_currSize++;

    // push the bound
    tc.pushEnumSizeIndex();

    // TODO: find "no more values" size?

    // restart with constructor class one (skip nullary constructors)
    d_consClassNum = 1;
    return increment();
  }

  bool incSuccess = false;
  do
  {
    // the children should be initialized by here
    Assert(d_childrenValid == d_ccTypes.size() + 1);

    // do we have more constructors for the given children?
    while (d_consNum < d_ccCons.size())
    {
      // increment constructor index
      // we will build for the current constructor and the given children
      d_consNum++;
      d_currTerm = Node::null();
      d_currTerm = getCurrent();
      if (tc.addTerm(d_currTerm))
      {
        return true;
      }
      // the term was not unique based on rewriting
    }

    // finished constructors for this set of children, must increment children

    // reset the constructor number
    d_consNum = 0;

    // try incrementing the last child until we find one that works
    incSuccess = false;
    while (!incSuccess && d_childrenValid > 0)
    {
      unsigned i = d_childrenValid - 1;
      Assert(d_children[i].getCurrentSize() <= d_currChildSize);
      // track the size
      d_currChildSize -= d_children[i].getCurrentSize();
      if (d_children[i].increment())
      {
        d_currChildSize += d_children[i].getCurrentSize();
        // must see if we can initialize the remaining children here
        // if not, there is no use continuing.
        if (initializeChildren())
        {
          Assert(d_currChildSize < d_currSize);
          incSuccess = true;
        }
      }
      if (!incSuccess)
      {
        // current child is out of values
        d_children.erase(i);
        d_childrenValid--;
      }
    }
  } while (incSuccess);

  // restart with the next constructor class
  d_ccCons.clear();
  d_ccTypes.clear();
  return increment();
}

bool SygusEnumerator::TermEnum::setNextEndIndex()
{
  SygusEnumerator::TermCache& tc = d_se->d_tcache[d_tn];
  // if we are at the beginning of the next size, increment current size
  while (d_index == d_indexNextEnd)
  {
    d_currSize++;
    // if we've hit the size limit, return false
    if (d_currSize == d_sizeLim)
    {
      return false;
    }
    // update the next end index
    d_indexNextEnd = tc.getIndexForSize(d_currSize + 1);
  }
  return true;
}

bool SygusEnumerator::TermEnum::initializeChildren()
{
  unsigned initValid = d_childrenValid;
  // while we need to initialize the current child
  while (d_childrenValid <= d_ccTypes.size())
  {
    if (!initializeChild(d_childrenValid))
    {
      // undo until previous initialized index
      while (d_childrenValid > initValid)
      {
        d_children.erase(d_childrenValid - 1);
        d_childrenValid--;
      }
      return false;
    }
    d_childrenValid++;
  }
  // initialized all children
  return true;
}

bool SygusEnumerator::TermEnum::initializeChild(unsigned i)
{
  Assert(d_currChildSize < d_currSize);
  TermEnum& te = d_children[i];
  bool init = false;
  // if we are the last child
  if (i + 1 == d_ccTypes.size())
  {
    // initialize the child to enumerate exactly the terms that sum to size
    init = te.initialize(
        d_se, d_ccTypes[i], (d_currSize - 1) - d_currChildSize, true);
  }
  else
  {
    // initialize the child to have limit (d_currSize-1)
    init = te.initialize(
        d_se, d_ccTypes[i], (d_currSize - 1) - d_currChildSize, false);
  }
  if (!init)
  {
    // failed to initialize
    d_children.erase(i);
    return false;
  }
  unsigned teSize = te.getCurrentSize();
  // fail if the initial children size does not fit d_currSize-1
  if (teSize + d_currChildSize >= d_currSize)
  {
    d_children.erase(i);
    return false;
  }
  d_currChildSize += teSize;
  return true;
}

SygusEnumerator::TermEnum* SygusEnumerator::getMasterEnumForType(TypeNode tn)
{
  if (d_masterEnum.find(tn) == d_masterEnum.end())
  {
    bool ret = d_masterEnum[tn].initializeMaster(this, tn);
    AlwaysAssert(ret);
  }
  return &d_masterEnum[tn];
}

}  // namespace quantifiers
}  // namespace theory
}  // namespace CVC4
