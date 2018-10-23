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

#include "options/datatypes_options.h"

using namespace CVC4::kind;

namespace CVC4 {
namespace theory {
namespace quantifiers {

SygusEnumerator::SygusEnumerator(TermDbSygus* tds, SynthConjecture * p)
    : d_tds(tds), d_parent(p), d_tlEnum(nullptr), d_abortSize(-1)
{
}

void SygusEnumerator::initialize(Node e)
{
  d_e = e;
  d_etype = d_e.getType();
  d_tlEnum = getMasterEnumForType(d_etype);
  d_abortSize = options::sygusAbortSize();
}

void SygusEnumerator::addValue(Node v)
{
  // do nothing
}

Node SygusEnumerator::getNext()
{
  int cs = static_cast<int>(d_tlEnum->getCurrentSize());
  if (d_tlEnum->increment())
  {
    if (d_abortSize >= 0 && cs > d_abortSize)
    {
      std::stringstream ss;
      ss << "Maximum term size (" << options::sygusAbortSize()
         << ") for enumerative SyGuS exceeded.";
      throw LogicException(ss.str());
    }
    Node ret = d_tlEnum->getCurrent();
    Trace("sygus-enum") << "Enumerate : " << d_tds->sygusToBuiltin(ret)
                        << std::endl;
    return ret;
  }
  return Node::null();
}

SygusEnumerator::TermCache::TermCache()
    : d_tds(nullptr), d_numConClasses(0), d_sizeEnum(0)
{
}
void SygusEnumerator::TermCache::initialize(TypeNode tn, TermDbSygus* tds)
{
  Trace("sygus-enum-debug") << "Init term cache " << tn << "..." << std::endl;
  d_tn = tn;
  d_tds = tds;
  d_sizeStartIndex[0] = 0;

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
  Trace("sygus-enum-debug") << "...finish" << std::endl;
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
  // the term size should match the size we are enumerating
  AlwaysAssert( d_tds->getSygusTermSize(n)==d_sizeEnum);
  Node bn = d_tds->sygusToBuiltin(n);
  bn = d_tds->getExtRewriter()->extendedRewrite(bn);
  // must be unique up to rewriting
  if (d_bterms.find(bn) != d_bterms.end())
  {
    return false;
  }
  /*
  if (options::sygusSymBreakPbe())
  {
    // Is it equivalent under examples?
    Node bnr = d_tds->getP->addSearchVal(d_tn, bn);
    if( bn!=bnr )
    {
      return false;
    }
  }
  */
  d_terms.push_back(n);
  d_bterms.insert(bn);
  return true;
}
void SygusEnumerator::TermCache::pushEnumSizeIndex()
{
  d_sizeEnum++;
  d_sizeStartIndex[d_sizeEnum] = d_terms.size();
  Trace("sygus-enum-debug") << "tc(" << d_tn << "): size " << d_sizeEnum << " terms start at index " << d_terms.size() << std::endl;
}
unsigned SygusEnumerator::TermCache::getEnumSize() const { return d_sizeEnum; }
unsigned SygusEnumerator::TermCache::getIndexForSize(unsigned s) const
{
  Assert(s <= d_sizeEnum);
  std::map<unsigned, unsigned>::const_iterator it = d_sizeStartIndex.find(s);
  Assert(it != d_sizeStartIndex.end());
  return it->second;
}
Node SygusEnumerator::TermCache::getTerm(unsigned index) const
{
  Assert(index < d_terms.size());
  return d_terms[index];
}

unsigned SygusEnumerator::TermCache::getNumTerms() const
{
  return d_terms.size();
}

unsigned SygusEnumerator::TermEnum::getCurrentSize() { return d_currSize; }

SygusEnumerator::TermEnum::TermEnum() : d_se(nullptr), d_currSize(0) {}

SygusEnumerator::TermEnumSlave::TermEnumSlave()
    : TermEnum(), d_sizeLim(0), d_index(0), d_indexNextEnd(0), d_master(nullptr)
{
}

bool SygusEnumerator::TermEnumSlave::initialize(SygusEnumerator* se,
                                                TypeNode tn,
                                                unsigned sizeLim,
                                                bool sizeExact)
{
  d_se = se;
  d_tn = tn;
  d_sizeLim = sizeLim;
  Trace("sygus-enum-debug2") << "slave(" << d_tn << "): init, bound=" << sizeLim << ", exact=" << sizeExact << "...\n";

  // must have pointer to the master
  d_master = d_se->getMasterEnumForType(d_tn);

  SygusEnumerator::TermCache& tc = d_se->d_tcache[d_tn];
  // if the size is exact, we start at the limit
  d_currSize = sizeExact ? sizeLim : 0;
  // initialize the index
  while (d_currSize > tc.getEnumSize())
  {
    Trace("sygus-enum-debug2") << "slave(" << d_tn << "): init force increment master...\n";
    // increment the master until we have enough terms
    if (!d_master->increment())
    {
      Trace("sygus-enum-debug2") << "slave(" << d_tn << "): ...fail init force master\n";
      return false;
    }
    Trace("sygus-enum-debug2") << "slave(" << d_tn << "): ...success init force master\n";
  }
  d_index = tc.getIndexForSize(d_currSize);
  Trace("sygus-enum-debug2") << "slave(" << d_tn << "): validate indices...\n";
  // initialize the next end index (marks where size increments)
  validateIndexNextEnd();
  Trace("sygus-enum-debug2") << "slave(" << d_tn << "): validate init end: " << d_hasIndexNextEnd << " " << d_indexNextEnd << " " << d_index << " " << d_currSize << "\n";
  // ensure that indexNextEnd is valid (it must be greater than d_index)
  bool ret = validateIndex();
  Trace("sygus-enum-debug2") << "slave(" << d_tn << "): ...success init, now: " << d_hasIndexNextEnd << " " << d_indexNextEnd << " " << d_index << " " << d_currSize << "\n";
  return ret;
}

Node SygusEnumerator::TermEnumSlave::getCurrent()
{
  SygusEnumerator::TermCache& tc = d_se->d_tcache[d_tn];
  Node curr = tc.getTerm(d_index);
  Trace("sygus-enum-debug2") << "slave(" << d_tn << "): current : " << d_se->d_tds->sygusToBuiltin(curr) << ", sizes = " << d_se->d_tds->getSygusTermSize(curr) << " " << getCurrentSize() << std::endl;
  Trace("sygus-enum-debug2") << "slave(" << d_tn << "): indices : " << d_hasIndexNextEnd << " " << d_indexNextEnd << " " << d_index << std::endl;
  AlwaysAssert( d_se->d_tds->getSygusTermSize(curr)==getCurrentSize() );
  // lookup in the cache
  return tc.getTerm(d_index);
}

bool SygusEnumerator::TermEnumSlave::increment()
{
  // increment index
  d_index++;
  // ensure that index is valid
  return validateIndex();
}

bool SygusEnumerator::TermEnumSlave::validateIndex()
{
  Trace("sygus-enum-debug2") << "slave(" << d_tn << ") : validate index...\n";
  SygusEnumerator::TermCache& tc = d_se->d_tcache[d_tn];
  // ensure that index is in the range
  if (d_index >= tc.getNumTerms())
  {
    Trace("sygus-enum-debug2") << "slave(" << d_tn << ") : force master...\n";
    // must push the master index
    if (!d_master->increment())
    {
      Trace("sygus-enum-debug2")
          << "slave(" << d_tn << ") : ...fail force master\n";
      return false;
    }
    Trace("sygus-enum-debug2") << "slave(" << d_tn << ") : ...success force master\n";
  }
  // always validate the next index end here
  validateIndexNextEnd();
  Trace("sygus-enum-debug2")
      << "slave(" << d_tn << ") : validate index end...\n";
  // if we are at the beginning of the next size, increment current size
  while (d_hasIndexNextEnd && d_index == d_indexNextEnd)
  {
    d_currSize++;
    Trace("sygus-enum-debug2") << "slave(" << d_tn << ") : size++ ("
                               << d_currSize << "/" << d_sizeLim << ")\n";
    // if we've hit the size limit, return false
    if (d_currSize > d_sizeLim)
    {
      Trace("sygus-enum-debug2") << "slave(" << d_tn << ") : fail size\n";
      return false;
    }
    validateIndexNextEnd();
  }
  Trace("sygus-enum-debug2") << "slave(" << d_tn << ") : finished\n";
  return true;
}

void SygusEnumerator::TermEnumSlave::validateIndexNextEnd()
{
  SygusEnumerator::TermCache& tc = d_se->d_tcache[d_tn];
  // update the next end index
  d_hasIndexNextEnd = d_currSize < tc.getEnumSize();
  if (d_hasIndexNextEnd)
  {
    d_indexNextEnd = tc.getIndexForSize(d_currSize + 1);
  }
}

SygusEnumerator::TermEnumMaster* SygusEnumerator::getMasterEnumForType(
    TypeNode tn)
{
  if (d_masterEnum.find(tn) == d_masterEnum.end())
  {
    // initialize the term cache
    d_tcache[tn].initialize(tn, d_tds);
    // initialize the master enumerator
    bool ret = d_masterEnum[tn].initialize(this, tn);
    AlwaysAssert(ret);
  }
  return &d_masterEnum[tn];
}

SygusEnumerator::TermEnumMaster::TermEnumMaster()
    : TermEnum(),
      d_isIncrementing(false),
      d_consClassNum(0),
      d_consNum(0),
      d_currChildSize(0),
      d_childrenValid(0),
      d_lastSize(0)
{
}

bool SygusEnumerator::TermEnumMaster::initialize(SygusEnumerator* se,
                                                 TypeNode tn)
{
  Trace("sygus-enum-debug") << "master(" << tn << "): init...\n";
  d_se = se;
  d_tn = tn;

  d_currSize = 0;
  d_lastSize = 0;
  // we will start with constructor class zero
  d_consClassNum = 0;
  d_ccCons.clear();
  d_isIncrementing = false;
  bool ret = increment();
  Trace("sygus-enum-debug") << "master(" << tn << "): finish init\n";
  return ret;
}

Node SygusEnumerator::TermEnumMaster::getCurrent()
{
  if (!d_currTerm.isNull())
  {
    return d_currTerm;
  }
  SygusEnumerator::TermCache& tc = d_se->d_tcache[d_tn];
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
  d_currTerm = NodeManager::currentNM()->mkNode(APPLY_CONSTRUCTOR, children);
  return d_currTerm;
}

bool SygusEnumerator::TermEnumMaster::increment()
{
  // am I already incrementing? if so, fail
  if (d_isIncrementing)
  {
    return false;
  }
  // This is to break infinite loops for slave enumerators who request an
  // increment() from the master enumerator of their type that is also their
  // parent. This ensures we do not loop on a grammar like:
  //   A -> -( A ) | B+B
  //   B -> x | y
  // where we require the first term enumerated to be over B+B.
  // Set that we are incrementing
  d_isIncrementing = true;
  bool ret = incrementInternal();
  d_isIncrementing = false;
  return ret;
}

bool SygusEnumerator::TermEnumMaster::incrementInternal()
{
  SygusEnumerator::TermCache& tc = d_se->d_tcache[d_tn];

  // the maximum index of a constructor class to consider
  unsigned ncc = d_currSize == 0 ? 1 : tc.getNumConstructorClasses();

  // have we initialized the current constructor class?
  while (d_ccCons.empty() && d_consClassNum < ncc)
  {
    Assert( d_ccTypes.empty() );
    Trace("sygus-enum-debug2")
        << "master(" << d_tn << "): try constructor class " << d_consClassNum
        << std::endl;
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
        Trace("sygus-enum-debug2")
            << "master(" << d_tn << "): failed due to init size\n";
      }
    }
    else
    {
      Trace("sygus-enum-debug2")
          << "master(" << d_tn << "): failed due to no cons\n";
    }
    // increment the next constructor class we will try
    d_consClassNum++;
  }

  // have we run out of constructor classes for this size?
  if (d_ccCons.empty())
  {
    // "no more values" size? FIXME
    if( d_lastSize+100<d_currSize )
    {
      return false;
    }
    
    // increment the size bound
    d_currSize++;
    Trace("sygus-enum-debug2") << "master(" << d_tn << "): size++ : " << d_currSize << "\n";
    if( Trace.isOn("cegqi-engine") )
    {
      // am i the master enumerator? if so, print 
      if( d_se->d_tlEnum==this )
      {
        Trace("cegqi-engine") << "SygusEnumerator::size = " << d_currSize << std::endl;
      }
    }

    // push the bound
    tc.pushEnumSizeIndex();

    // restart with constructor class one (skip nullary constructors)
    d_consClassNum = 1;
    return incrementInternal();
  }

  bool incSuccess = false;
  do
  {
    Trace("sygus-enum-debug2") << "master(" << d_tn << "): check return " << d_childrenValid << "/" << d_ccTypes.size() << std::endl;
    // the children should be initialized by here
    Assert(d_childrenValid == d_ccTypes.size());

    // do we have more constructors for the given children?
    while (d_consNum < d_ccCons.size())
    {
      Trace("sygus-enum-debug2") << "master(" << d_tn << "): try constructor "
                                 << d_consNum << std::endl;
      // increment constructor index
      // we will build for the current constructor and the given children
      d_consNum++;
      d_currTerm = Node::null();
      Node c = getCurrent();
      if (tc.addTerm(c))
      {
        d_lastSize = d_currSize;
        return true;
      }
      Trace("sygus-enum-debug2") << "master(" << d_tn << "): failed addTerm\n";
      // the term was not unique based on rewriting
    }

    // finished constructors for this set of children, must increment children

    // reset the constructor number
    d_consNum = 0;

    // try incrementing the last child until we find one that works
    incSuccess = false;
    while (!incSuccess && d_childrenValid > 0)
    {
      Trace("sygus-enum-debug2") << "master(" << d_tn << "): try incrementing "
                                 << d_childrenValid << std::endl;
      unsigned i = d_childrenValid - 1;
      Assert(d_children[i].getCurrentSize() <= d_currChildSize);
      // track the size
      d_currChildSize -= d_children[i].getCurrentSize();
      if (d_children[i].increment())
      {
        Trace("sygus-enum-debug2")
            << "master(" << d_tn << "): increment success...\n";
        d_currChildSize += d_children[i].getCurrentSize();
        // must see if we can initialize the remaining children here
        // if not, there is no use continuing.
        if (initializeChildren())
        {
          Trace("sygus-enum-debug2") << "master(" << d_tn << "): success\n";
          Assert(d_currChildSize < d_currSize);
          incSuccess = true;
        }
      }
      if (!incSuccess)
      {
        Trace("sygus-enum-debug2")
            << "master(" << d_tn << "): fail, backtrack...\n";
        // current child is out of values
        d_children.erase(i);
        d_childrenValid--;
      }
    }
  } while (incSuccess);
  Trace("sygus-enum-debug2")
      << "master(" << d_tn << "): failed increment children\n";
  // restart with the next constructor class
  d_ccCons.clear();
  d_ccTypes.clear();
  return incrementInternal();
}

bool SygusEnumerator::TermEnumMaster::initializeChildren()
{
  Trace("sygus-enum-debug2")
      << "master(" << d_tn << "): init children, start = " << d_childrenValid
      << ", #types=" << d_ccTypes.size() << ", sizes=" << d_currChildSize << "/" << d_currSize << std::endl;
  unsigned initValid = d_childrenValid;
  // while we need to initialize the current child
  while (d_childrenValid < d_ccTypes.size())
  {
    if (!initializeChild(d_childrenValid))
    {
      Trace("sygus-enum-debug2")
          << "master(" << d_tn << "): init children : failed" << std::endl;
      // undo until previous initialized index
      while (d_childrenValid > initValid)
      {
        d_children.erase(d_childrenValid - 1);
        d_childrenValid--;
      }
      Trace("sygus-enum-debug2")
          << "master(" << d_tn << "): init children : failed, finished"
          << std::endl;
      return false;
    }
    d_childrenValid++;
  }
  Trace("sygus-enum-debug2")
      << "master(" << d_tn << "): init children : success" << std::endl;
  // initialized all children
  return true;
}

bool SygusEnumerator::TermEnumMaster::initializeChild(unsigned i)
{
  Assert(d_currChildSize < d_currSize);
  TermEnumSlave& te = d_children[i];
  bool lastChild = (i + 1 == d_ccTypes.size());
  // initialize the child to enumerate exactly the terms that sum to size
  bool init = te.initialize(
      d_se, d_ccTypes[i], (d_currSize - 1) - d_currChildSize, lastChild);
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

}  // namespace quantifiers
}  // namespace theory
}  // namespace CVC4
