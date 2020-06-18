/*********************                                                        */
/*! \file sygus_enumerator.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Mathias Preiner
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Implementation of sygus_enumerator
 **/

#include "theory/quantifiers/sygus/sygus_enumerator.h"

#include "options/datatypes_options.h"
#include "options/quantifiers_options.h"
#include "theory/datatypes/theory_datatypes_utils.h"
#include "theory/quantifiers/sygus/synth_engine.h"

using namespace CVC4::kind;

namespace CVC4 {
namespace theory {
namespace quantifiers {

SygusEnumerator::SygusEnumerator(TermDbSygus* tds,
                                 SynthConjecture* p,
                                 SygusStatistics& s)
    : d_tds(tds), d_parent(p), d_stats(s), d_tlEnum(nullptr), d_abortSize(-1)
{
}

void SygusEnumerator::initialize(Node e)
{
  Trace("sygus-enum") << "SygusEnumerator::initialize " << e << std::endl;
  d_enum = e;
  d_etype = d_enum.getType();
  Assert(d_etype.isDatatype());
  Assert(d_etype.getDType().isSygus());
  d_tlEnum = getMasterEnumForType(d_etype);
  d_abortSize = options::sygusAbortSize();

  // Get the statically registered symmetry breaking clauses for e, see if they
  // can be used for speeding up the enumeration.
  NodeManager* nm = NodeManager::currentNM();
  std::vector<Node> sbl;
  d_tds->getSymBreakLemmas(e, sbl);
  Node ag = d_tds->getActiveGuardForEnumerator(e);
  Node truen = nm->mkConst(true);
  // use TNode for substitute below
  TNode agt = ag;
  TNode truent = truen;
  Assert(d_tcache.find(d_etype) != d_tcache.end());
  const DType& dt = d_etype.getDType();
  for (const Node& lem : sbl)
  {
    if (!d_tds->isSymBreakLemmaTemplate(lem))
    {
      // substitute its active guard by true and rewrite
      Node slem = lem.substitute(agt, truent);
      slem = Rewriter::rewrite(slem);
      // break into conjuncts
      std::vector<Node> sblc;
      if (slem.getKind() == AND)
      {
        for (const Node& slemc : slem)
        {
          sblc.push_back(slemc);
        }
      }
      else
      {
        sblc.push_back(slem);
      }
      for (const Node& sblemma : sblc)
      {
        Trace("sygus-enum")
            << "  symmetry breaking lemma : " << sblemma << std::endl;
        // if its a negation of a unit top-level tester, then this specifies
        // that we should not enumerate terms whose top symbol is that
        // constructor
        if (sblemma.getKind() == NOT)
        {
          Node a;
          int tst = datatypes::utils::isTester(sblemma[0], a);
          if (tst >= 0)
          {
            if (a == e)
            {
              Node cons = dt[tst].getConstructor();
              Trace("sygus-enum") << "  ...unit exclude constructor #" << tst
                                  << ", constructor " << cons << std::endl;
              d_sbExcTlCons.insert(cons);
            }
          }
        }
        // other symmetry breaking lemmas such as disjunctions are not used
      }
    }
  }
}

void SygusEnumerator::addValue(Node v)
{
  // do nothing
}

bool SygusEnumerator::increment() { return d_tlEnum->increment(); }
Node SygusEnumerator::getCurrent()
{
  if (d_abortSize >= 0)
  {
    int cs = static_cast<int>(d_tlEnum->getCurrentSize());
    if (cs > d_abortSize)
    {
      std::stringstream ss;
      ss << "Maximum term size (" << options::sygusAbortSize()
         << ") for enumerative SyGuS exceeded.";
      throw LogicException(ss.str());
    }
  }
  Node ret = d_tlEnum->getCurrent();
  if (!ret.isNull() && !d_sbExcTlCons.empty())
  {
    Assert(ret.hasOperator());
    // might be excluded by an externally provided symmetry breaking clause
    if (d_sbExcTlCons.find(ret.getOperator()) != d_sbExcTlCons.end())
    {
      Trace("sygus-enum-exc")
          << "Exclude (external) : " << d_tds->sygusToBuiltin(ret) << std::endl;
      ret = Node::null();
    }
  }
  if (Trace.isOn("sygus-enum"))
  {
    Trace("sygus-enum") << "Enumerate : ";
    TermDbSygus::toStreamSygus("sygus-enum", ret);
    Trace("sygus-enum") << std::endl;
  }
  return ret;
}

SygusEnumerator::TermCache::TermCache()
    : d_tds(nullptr),
      d_eec(nullptr),
      d_isSygusType(false),
      d_numConClasses(0),
      d_sizeEnum(0),
      d_isComplete(false),
      d_sampleRrVInit(false)
{
}

void SygusEnumerator::TermCache::initialize(SygusStatistics* s,
                                            Node e,
                                            TypeNode tn,
                                            TermDbSygus* tds,
                                            ExampleEvalCache* eec)
{
  Trace("sygus-enum-debug") << "Init term cache " << tn << "..." << std::endl;
  d_stats = s;
  d_enum = e;
  d_tn = tn;
  d_tds = tds;
  d_eec = eec;
  d_sizeStartIndex[0] = 0;
  d_isSygusType = false;

  // compute static information about tn
  if (!d_tn.isDatatype())
  {
    // not a datatype, finish
    return;
  }
  const DType& dt = tn.getDType();
  if (!dt.isSygus())
  {
    // not a sygus datatype, finish
    return;
  }

  d_isSygusType = true;

  // get argument types for all constructors
  std::map<unsigned, std::vector<TypeNode>> argTypes;
  // map weights to constructors
  std::map<unsigned, std::vector<unsigned>> weightsToIndices;

  // constructor class 0 is reserved for nullary operators with 0 weight
  // this is an optimization so that we always skip them for sizes >= 1
  ConstructorClass& ccZero = d_cclass[0];
  ccZero.d_weight = 0;
  d_numConClasses = 1;
  // we must indicate that we should process zero weight constructor classes
  weightsToIndices[0].clear();
  for (unsigned i = 0, ncons = dt.getNumConstructors(); i < ncons; i++)
  {
    // record weight information
    unsigned w = dt[i].getWeight();
    Trace("sygus-enum-debug") << "Weight " << dt[i].getSygusOp() << ": " << w
                              << std::endl;
    weightsToIndices[w].push_back(i);
    // record type information
    for (unsigned j = 0, nargs = dt[i].getNumArgs(); j < nargs; j++)
    {
      TypeNode type = dt[i].getArgType(j);
      argTypes[i].push_back(type);
    }
  }
  NodeManager* nm = NodeManager::currentNM();
  for (std::pair<const unsigned, std::vector<unsigned>>& wp : weightsToIndices)
  {
    unsigned w = wp.first;

    // assign constructors to constructor classes
    TypeNodeIdTrie tnit;
    std::map<Node, unsigned> nToC;
    for (unsigned i : wp.second)
    {
      if (argTypes[i].empty() && w == 0)
      {
        ccZero.d_cons.push_back(i);
      }
      else
      {
        // we merge those whose argument types are the same
        // We could, but choose not to, order these types, which would lead to
        // more aggressive merging of constructor classes. On the negative side,
        // this adds another level of indirection to remember which argument
        // positions the argument types occur in, for each constructor.
        Node n = nm->mkConst(Rational(i));
        nToC[n] = i;
        tnit.add(n, argTypes[i]);
      }
    }
    std::map<Node, unsigned> assign;
    tnit.assignIds(assign, d_numConClasses);
    for (std::pair<const Node, unsigned>& cp : assign)
    {
      // determine which constructor class this goes into using tnit
      unsigned cclassi = cp.second;
      unsigned i = nToC[cp.first];
      Trace("sygus-enum-debug") << "Constructor class for "
                                << dt[i].getSygusOp() << " is " << cclassi
                                << std::endl;
      // initialize the constructor class
      if (d_cclass.find(cclassi) == d_cclass.end())
      {
        d_cclass[cclassi].d_weight = w;
        d_cclass[cclassi].d_types.insert(d_cclass[cclassi].d_types.end(),
                                         argTypes[i].begin(),
                                         argTypes[i].end());
      }
      // add to constructor class
      d_cclass[cclassi].d_cons.push_back(i);
    }
    Trace("sygus-enum-debug") << "#cons classes for weight <= " << w << " : "
                              << d_numConClasses << std::endl;
    d_weightToCcIndex[w] = d_numConClasses;
  }
  Trace("sygus-enum-debug") << "...finish" << std::endl;
}

unsigned SygusEnumerator::TermCache::getLastConstructorClassIndexForWeight(
    unsigned w) const
{
  std::map<unsigned, unsigned>::const_iterator it = d_weightToCcIndex.find(w);
  if (it == d_weightToCcIndex.end())
  {
    return d_numConClasses;
  }
  return it->second;
}
unsigned SygusEnumerator::TermCache::getNumConstructorClasses() const
{
  return d_numConClasses;
}
void SygusEnumerator::TermCache::getConstructorClass(
    unsigned i, std::vector<unsigned>& cclass) const
{
  std::map<unsigned, ConstructorClass>::const_iterator it = d_cclass.find(i);
  Assert(it != d_cclass.end());
  cclass.insert(
      cclass.end(), it->second.d_cons.begin(), it->second.d_cons.end());
}
void SygusEnumerator::TermCache::getTypesForConstructorClass(
    unsigned i, std::vector<TypeNode>& types) const
{
  std::map<unsigned, ConstructorClass>::const_iterator it = d_cclass.find(i);
  Assert(it != d_cclass.end());
  types.insert(
      types.end(), it->second.d_types.begin(), it->second.d_types.end());
}

unsigned SygusEnumerator::TermCache::getWeightForConstructorClass(
    unsigned i) const
{
  std::map<unsigned, ConstructorClass>::const_iterator it = d_cclass.find(i);
  Assert(it != d_cclass.end());
  return it->second.d_weight;
}

bool SygusEnumerator::TermCache::addTerm(Node n)
{
  if (!d_isSygusType)
  {
    // non-sygus terms generated by TermEnumMasterInterp/TermEnumMasterFv
    // enumeration are unique by construction
    Trace("sygus-enum-terms") << "tc(" << d_tn << "): term (builtin): " << n
                              << std::endl;
    d_terms.push_back(n);
    return true;
  }
  Assert(!n.isNull());
  if (options::sygusSymBreakDynamic())
  {
    Node bn = d_tds->sygusToBuiltin(n);
    Node bnr = d_tds->getExtRewriter()->extendedRewrite(bn);
    ++(d_stats->d_enumTermsRewrite);
    if (options::sygusRewVerify())
    {
      if (bn != bnr)
      {
        if (!d_sampleRrVInit)
        {
          d_sampleRrVInit = true;
          d_samplerRrV.initializeSygus(
              d_tds, d_enum, options::sygusSamples(), false);
        }
        d_samplerRrV.checkEquivalent(bn, bnr);
      }
    }
    // must be unique up to rewriting
    if (d_bterms.find(bnr) != d_bterms.end())
    {
      Trace("sygus-enum-exc") << "Exclude: " << bn << std::endl;
      return false;
    }
    // insert to builtin term cache, regardless of whether it is redundant
    // based on examples.
    d_bterms.insert(bnr);
    // if we are doing PBE symmetry breaking
    if (d_eec != nullptr)
    {
      ++(d_stats->d_enumTermsExampleEval);
      // Is it equivalent under examples?
      Node bne = d_eec->addSearchVal(d_tn, bnr);
      if (!bne.isNull())
      {
        if (bnr != bne)
        {
          Trace("sygus-enum-exc")
              << "Exclude (by examples): " << bn << ", since we already have "
              << bne << std::endl;
          return false;
        }
      }
    }
    Trace("sygus-enum-terms") << "tc(" << d_tn << "): term " << bn << std::endl;
  }
  ++(d_stats->d_enumTerms);
  d_terms.push_back(n);
  return true;
}
void SygusEnumerator::TermCache::pushEnumSizeIndex()
{
  d_sizeEnum++;
  d_sizeStartIndex[d_sizeEnum] = d_terms.size();
  Trace("sygus-enum-debug") << "tc(" << d_tn << "): size " << d_sizeEnum
                            << " terms start at index " << d_terms.size()
                            << std::endl;
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

bool SygusEnumerator::TermCache::isComplete() const { return d_isComplete; }
void SygusEnumerator::TermCache::setComplete() { d_isComplete = true; }
unsigned SygusEnumerator::TermEnum::getCurrentSize() { return d_currSize; }
SygusEnumerator::TermEnum::TermEnum() : d_se(nullptr), d_currSize(0) {}
SygusEnumerator::TermEnumSlave::TermEnumSlave()
    : TermEnum(),
      d_sizeLim(0),
      d_index(0),
      d_indexNextEnd(0),
      d_hasIndexNextEnd(false),
      d_master(nullptr)
{
}

bool SygusEnumerator::TermEnumSlave::initialize(SygusEnumerator* se,
                                                TypeNode tn,
                                                unsigned sizeMin,
                                                unsigned sizeMax)
{
  d_se = se;
  d_tn = tn;
  d_sizeLim = sizeMax;
  Trace("sygus-enum-debug2") << "slave(" << d_tn
                             << "): init, min/max=" << sizeMin << "/" << sizeMax
                             << "...\n";

  // must have pointer to the master
  d_master = d_se->getMasterEnumForType(d_tn);

  SygusEnumerator::TermCache& tc = d_se->d_tcache[d_tn];
  // if the size is exact, we start at the limit
  d_currSize = sizeMin;
  // initialize the index
  while (d_currSize > tc.getEnumSize())
  {
    Trace("sygus-enum-debug2") << "slave(" << d_tn
                               << "): init force increment master...\n";
    // increment the master until we have enough terms
    if (!d_master->increment())
    {
      Trace("sygus-enum-debug2") << "slave(" << d_tn
                                 << "): ...fail init force master\n";
      return false;
    }
    Trace("sygus-enum-debug2") << "slave(" << d_tn
                               << "): ...success init force master\n";
  }
  d_index = tc.getIndexForSize(d_currSize);
  Trace("sygus-enum-debug2") << "slave(" << d_tn << "): validate indices...\n";
  // initialize the next end index (marks where size increments)
  validateIndexNextEnd();
  Trace("sygus-enum-debug2")
      << "slave(" << d_tn << "): validate init end: " << d_hasIndexNextEnd
      << " " << d_indexNextEnd << " " << d_index << " " << d_currSize << "\n";
  // ensure that indexNextEnd is valid (it must be greater than d_index)
  bool ret = validateIndex();
  Trace("sygus-enum-debug2")
      << "slave(" << d_tn << "): ..." << (ret ? "success" : "fail")
      << " init, now: " << d_hasIndexNextEnd << " " << d_indexNextEnd << " "
      << d_index << " " << d_currSize << "\n";
  return ret;
}

Node SygusEnumerator::TermEnumSlave::getCurrent()
{
  SygusEnumerator::TermCache& tc = d_se->d_tcache[d_tn];
  Node curr = tc.getTerm(d_index);
  Trace("sygus-enum-debug2")
      << "slave(" << d_tn
      << "): current : " << d_se->d_tds->sygusToBuiltin(curr)
      << ", sizes = " << d_se->d_tds->getSygusTermSize(curr) << " "
      << getCurrentSize() << std::endl;
  Trace("sygus-enum-debug2") << "slave(" << d_tn
                             << "): indices : " << d_hasIndexNextEnd << " "
                             << d_indexNextEnd << " " << d_index << std::endl;
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
  while (d_index >= tc.getNumTerms())
  {
    Assert(d_index == tc.getNumTerms());
    Trace("sygus-enum-debug2") << "slave(" << d_tn << ") : force master...\n";
    // if the size of the master is larger than the size limit, then
    // there is no use continuing, since there are no more terms that this
    // slave enumerator can return.
    if (d_master->getCurrentSize() > d_sizeLim)
    {
      return false;
    }
    // must push the master index
    if (!d_master->increment())
    {
      Trace("sygus-enum-debug2") << "slave(" << d_tn
                                 << ") : ...fail force master\n";
      return false;
    }
    Trace("sygus-enum-debug2") << "slave(" << d_tn
                               << ") : ...success force master\n";
  }
  // always validate the next index end here
  validateIndexNextEnd();
  Trace("sygus-enum-debug2") << "slave(" << d_tn
                             << ") : validate index end...\n";
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

void SygusEnumerator::initializeTermCache(TypeNode tn)
{
  // initialize the term cache
  // see if we use an example evaluation cache for symmetry breaking
  ExampleEvalCache* eec = nullptr;
  if (d_parent != nullptr && options::sygusSymBreakPbe())
  {
    eec = d_parent->getExampleEvalCache(d_enum);
  }
  d_tcache[tn].initialize(&d_stats, d_enum, tn, d_tds, eec);
}

SygusEnumerator::TermEnum* SygusEnumerator::getMasterEnumForType(TypeNode tn)
{
  if (tn.isDatatype() && tn.getDType().isSygus())
  {
    std::map<TypeNode, TermEnumMaster>::iterator it = d_masterEnum.find(tn);
    if (it != d_masterEnum.end())
    {
      return &it->second;
    }
    initializeTermCache(tn);
    // initialize the master enumerator
    bool ret = d_masterEnum[tn].initialize(this, tn);
    AlwaysAssert(ret);
    return &d_masterEnum[tn];
  }
  if (options::sygusRepairConst())
  {
    std::map<TypeNode, TermEnumMasterFv>::iterator it = d_masterEnumFv.find(tn);
    if (it != d_masterEnumFv.end())
    {
      return &it->second;
    }
    initializeTermCache(tn);
    // initialize the master enumerator
    bool ret = d_masterEnumFv[tn].initialize(this, tn);
    AlwaysAssert(ret);
    return &d_masterEnumFv[tn];
  }
  std::map<TypeNode, std::unique_ptr<TermEnumMasterInterp>>::iterator it =
      d_masterEnumInt.find(tn);
  if (it != d_masterEnumInt.end())
  {
    return it->second.get();
  }
  initializeTermCache(tn);
  // create the master enumerator
  d_masterEnumInt[tn].reset(new TermEnumMasterInterp(tn));
  // initialize the master enumerator
  TermEnumMasterInterp* temi = d_masterEnumInt[tn].get();
  bool ret = temi->initialize(this, tn);
  AlwaysAssert(ret);
  return temi;
}

SygusEnumerator::TermEnumMaster::TermEnumMaster()
    : TermEnum(),
      d_isIncrementing(false),
      d_currTermSet(false),
      d_consClassNum(0),
      d_ccWeight(0),
      d_consNum(0),
      d_currChildSize(0),
      d_childrenValid(0)
{
}

bool SygusEnumerator::TermEnumMaster::initialize(SygusEnumerator* se,
                                                 TypeNode tn)
{
  Trace("sygus-enum-debug") << "master(" << tn << "): init...\n";
  d_se = se;
  d_tn = tn;

  d_currSize = 0;
  // we will start with constructor class zero
  d_consClassNum = 0;
  d_currChildSize = 0;
  d_ccCons.clear();
  d_isIncrementing = false;
  d_currTermSet = false;
  bool ret = increment();
  Trace("sygus-enum-debug") << "master(" << tn
                            << "): finish init, ret = " << ret << "\n";
  return ret;
}

Node SygusEnumerator::TermEnumMaster::getCurrent()
{
  if (d_currTermSet)
  {
    return d_currTerm;
  }
  d_currTermSet = true;
  // construct based on the children
  std::vector<Node> children;
  const DType& dt = d_tn.getDType();
  Assert(d_consNum > 0 && d_consNum <= d_ccCons.size());
  // get the current constructor number
  unsigned cnum = d_ccCons[d_consNum - 1];
  children.push_back(dt[cnum].getConstructor());
  // add the current of each child to children
  for (unsigned i = 0, nargs = dt[cnum].getNumArgs(); i < nargs; i++)
  {
    Assert(d_children.find(i) != d_children.end());
    Node cc = d_children[i].getCurrent();
    if (cc.isNull())
    {
      d_currTerm = cc;
      return cc;
    }
    children.push_back(cc);
  }
  d_currTerm = NodeManager::currentNM()->mkNode(APPLY_CONSTRUCTOR, children);
  return d_currTerm;
}

bool SygusEnumerator::TermEnumMaster::increment()
{
  // Am I already incrementing? If so, fail.
  // This is to break infinite loops for slave enumerators who request an
  // increment() from the master enumerator of their type that is also their
  // parent. This ensures we do not loop on a grammar like:
  //   A -> -( A ) | B+B
  //   B -> x | y
  // where we require the first term enumerated to be over B+B.
  // Set that we are incrementing
  if (d_isIncrementing)
  {
    return false;
  }
  Trace("sygus-enum-summary") << "SygusEnumerator::TermEnumMaster: increment "
                              << d_tn << "..." << std::endl;
  d_isIncrementing = true;
  bool ret = incrementInternal();
  d_isIncrementing = false;
  Trace("sygus-enum-summary")
      << "SygusEnumerator::TermEnumMaster: finished increment " << d_tn
      << std::endl;
  return ret;
}

bool SygusEnumerator::TermEnumMaster::incrementInternal()
{
  SygusEnumerator::TermCache& tc = d_se->d_tcache[d_tn];
  if (tc.isComplete())
  {
    return false;
  }
  Trace("sygus-enum-debug2") << "master(" << d_tn
                             << "): get last constructor class..." << std::endl;
  // the maximum index of a constructor class to consider
  unsigned ncc = tc.getLastConstructorClassIndexForWeight(d_currSize);
  Trace("sygus-enum-debug2") << "Last constructor class " << d_currSize << ": "
                             << ncc << std::endl;

  // have we initialized the current constructor class?
  while (d_ccCons.empty() && d_consClassNum < ncc)
  {
    Assert(d_ccTypes.empty());
    Trace("sygus-enum-debug2") << "master(" << d_tn
                               << "): try constructor class " << d_consClassNum
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
      d_ccWeight = tc.getWeightForConstructorClass(d_consClassNum);
      d_childrenValid = 0;
      // initialize the children into their initial state
      if (!initializeChildren())
      {
        // didn't work (due to size), we will try the next class
        d_ccCons.clear();
        d_ccTypes.clear();
        Trace("sygus-enum-debug2") << "master(" << d_tn
                                   << "): failed due to init size\n";
      }
    }
    else
    {
      // No constructors in constructor class. This can happen for class 0 if a
      // type has no nullary constructors with weight 0.
      Trace("sygus-enum-debug2") << "master(" << d_tn
                                 << "): failed due to no cons\n";
    }
    // increment the next constructor class we will try
    d_consClassNum++;
  }

  // have we run out of constructor classes for this size?
  if (d_ccCons.empty())
  {
    // check whether we should terminate
    if (d_tn.isInterpretedFinite())
    {
      if (ncc == tc.getNumConstructorClasses())
      {
        bool doTerminate = true;
        for (unsigned i = 1; i < ncc; i++)
        {
          // The maximum size of terms from a constructor class can be
          // determined if all of its argument types are finished enumerating.
          // If this maximum size is less than or equal to d_currSize for
          // each constructor class, we are done.
          unsigned sum = tc.getWeightForConstructorClass(i);
          std::vector<TypeNode> cctns;
          tc.getTypesForConstructorClass(i, cctns);
          for (unsigned j = 0, ntypes = cctns.size(); j < ntypes; j++)
          {
            TypeNode tnc = cctns[j];
            SygusEnumerator::TermCache& tcc = d_se->d_tcache[tnc];
            if (!tcc.isComplete())
            {
              // maximum size of this constructor class cannot be determined
              doTerminate = false;
              break;
            }
            else
            {
              sum += tcc.getEnumSize();
              if (sum > d_currSize)
              {
                // maximum size of this constructor class is greater than size
                doTerminate = false;
                break;
              }
            }
          }
          if (!doTerminate)
          {
            break;
          }
        }
        if (doTerminate)
        {
          Trace("sygus-engine") << "master(" << d_tn << "): complete at size "
                                << d_currSize << std::endl;
          tc.setComplete();
          return false;
        }
      }
    }

    // increment the size bound
    d_currSize++;
    Trace("sygus-enum-debug2") << "master(" << d_tn
                               << "): size++ : " << d_currSize << "\n";
    if (Trace.isOn("sygus-engine"))
    {
      // am i the master enumerator? if so, print
      if (d_se->d_tlEnum == this)
      {
        Trace("sygus-engine") << "SygusEnumerator::size = " << d_currSize
                              << std::endl;
      }
    }

    // push the bound
    tc.pushEnumSizeIndex();

    // restart with constructor class one (skip nullary constructors)
    d_consClassNum = 1;

    // We break for a round: return the null term when we cross a size
    // boundary. This ensures that the necessary breaks are taken, e.g.
    // in slave enumerators who may instead want to abandon this call to
    // increment master when the size of the master makes their increment
    // infeasible.
    d_currTermSet = true;
    d_currTerm = Node::null();
    return true;
  }

  bool incSuccess = false;
  do
  {
    Trace("sygus-enum-debug2") << "master(" << d_tn << "): check return "
                               << d_childrenValid << "/" << d_ccTypes.size()
                               << std::endl;
    // the children should be initialized by here
    Assert(d_childrenValid == d_ccTypes.size());

    // do we have more constructors for the given children?
    if (d_consNum < d_ccCons.size())
    {
      Trace("sygus-enum-debug2") << "master(" << d_tn << "): try constructor "
                                 << d_consNum << std::endl;
      // increment constructor index
      // we will build for the current constructor and the given children
      d_consNum++;
      d_currTermSet = false;
      d_currTerm = Node::null();
      Node c = getCurrent();
      if (!c.isNull())
      {
        if (!tc.addTerm(c))
        {
          // the term was not unique based on rewriting
          Trace("sygus-enum-debug2") << "master(" << d_tn
                                     << "): failed addTerm\n";
          // we will return null (d_currTermSet is true at this point)
          Assert(d_currTermSet);
          d_currTerm = Node::null();
        }
      }
      return true;
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
        Trace("sygus-enum-debug2") << "master(" << d_tn
                                   << "): increment success...\n";
        d_currChildSize += d_children[i].getCurrentSize();
        // must see if we can initialize the remaining children here
        // if not, there is no use continuing.
        if (initializeChildren())
        {
          Trace("sygus-enum-debug2")
              << "master(" << d_tn << "): success init children\n";
          Assert(d_currChildSize + d_ccWeight <= d_currSize);
          incSuccess = true;
        }
        else
        {
          // failed to initialize the remaining children (likely due to a
          // child having a non-zero minimum size bound).
          Trace("sygus-enum-debug2")
              << "master(" << d_tn << "): fail init children\n";
          d_currChildSize -= d_children[i].getCurrentSize();
        }
      }
      if (!incSuccess)
      {
        Trace("sygus-enum-debug2") << "master(" << d_tn
                                   << "): fail, backtrack...\n";
        // current child is out of values
        d_children.erase(i);
        d_childrenValid--;
      }
    }
  } while (incSuccess);
  Trace("sygus-enum-debug2") << "master(" << d_tn
                             << "): failed increment children\n";
  // restart with the next constructor class
  d_ccCons.clear();
  d_ccTypes.clear();
  return incrementInternal();
}

bool SygusEnumerator::TermEnumMaster::initializeChildren()
{
  Trace("sygus-enum-debug2")
      << "master(" << d_tn << "): init children, start = " << d_childrenValid
      << ", #types=" << d_ccTypes.size() << ", sizes=" << d_currChildSize << "/"
      << d_currSize << std::endl;
  unsigned currChildren = d_childrenValid;
  unsigned sizeMin = 0;
  // while we need to initialize the current child
  while (d_childrenValid < d_ccTypes.size())
  {
    if (!initializeChild(d_childrenValid, sizeMin))
    {
      if (d_childrenValid == currChildren)
      {
        // we are back to the child we started with, we terminate now.
        Trace("sygus-enum-debug2") << "master(" << d_tn
                                   << "): init children : failed, finished"
                                   << std::endl;
        return false;
      }
      Trace("sygus-enum-debug2") << "master(" << d_tn
                                 << "): init children : failed" << std::endl;
      // we failed in this size configuration
      // reinitialize with the next size up
      unsigned currSize = d_children[d_childrenValid - 1].getCurrentSize();
      d_currChildSize -= currSize;
      sizeMin = currSize + 1;
      d_children.erase(d_childrenValid - 1);
      d_childrenValid--;
    }
    else
    {
      sizeMin = 0;
      d_childrenValid++;
    }
  }
  Trace("sygus-enum-debug2") << "master(" << d_tn
                             << "): init children : success" << std::endl;
  // initialized all children
  return true;
}

bool SygusEnumerator::TermEnumMaster::initializeChild(unsigned i,
                                                      unsigned sizeMin)
{
  Assert(d_ccWeight <= d_currSize);
  Assert(d_currChildSize + d_ccWeight <= d_currSize);
  unsigned sizeMax = (d_currSize - d_ccWeight) - d_currChildSize;
  Trace("sygus-enum-debug2") << "master(" << d_tn << "): initializeChild " << i
                             << " (" << d_currSize << ", " << d_ccWeight << ", "
                             << d_currChildSize << ")\n";
  if (sizeMin > sizeMax)
  {
    Trace("sygus-enum-debug2") << "master(" << d_tn << "): failed due to size "
                               << sizeMin << "/" << sizeMax << "\n";
    return false;
  }
  // initialize the child to enumerate exactly the terms that sum to size
  sizeMin = (i + 1 == d_ccTypes.size()) ? sizeMax : sizeMin;
  TermEnumSlave& te = d_children[i];
  bool init = te.initialize(d_se, d_ccTypes[i], sizeMin, sizeMax);
  if (!init)
  {
    // failed to initialize
    d_children.erase(i);
    Trace("sygus-enum-debug2") << "master(" << d_tn
                               << "): failed due to child init\n";
    return false;
  }
  unsigned teSize = te.getCurrentSize();
  // fail if the initial children size does not fit d_currSize-d_ccWeight
  if (teSize + d_currChildSize + d_ccWeight > d_currSize)
  {
    d_children.erase(i);
    Trace("sygus-enum-debug2") << "master(" << d_tn
                               << "): failed due to child size\n";
    return false;
  }
  d_currChildSize += teSize;
  Trace("sygus-enum-debug2") << "master(" << d_tn
                             << "): success initializeChild " << i << "\n";
  return true;
}

SygusEnumerator::TermEnumMasterInterp::TermEnumMasterInterp(TypeNode tn)
    : TermEnum(), d_te(tn), d_currNumConsts(0), d_nextIndexEnd(0)
{
}

bool SygusEnumerator::TermEnumMasterInterp::initialize(SygusEnumerator* se,
                                                       TypeNode tn)
{
  d_se = se;
  d_tn = tn;
  d_currSize = 0;
  d_currNumConsts = 1;
  d_nextIndexEnd = 1;
  return true;
}

Node SygusEnumerator::TermEnumMasterInterp::getCurrent() { return *d_te; }
bool SygusEnumerator::TermEnumMasterInterp::increment()
{
  if (d_te.isFinished())
  {
    return false;
  }
  SygusEnumerator::TermCache& tc = d_se->d_tcache[d_tn];
  Node curr = getCurrent();
  tc.addTerm(curr);
  if (tc.getNumTerms() == d_nextIndexEnd)
  {
    tc.pushEnumSizeIndex();
    d_currSize++;
    d_currNumConsts = d_currNumConsts * options::sygusActiveGenEnumConsts();
    d_nextIndexEnd = d_nextIndexEnd + d_currNumConsts;
  }
  ++d_te;
  return !d_te.isFinished();
}
SygusEnumerator::TermEnumMasterFv::TermEnumMasterFv() : TermEnum() {}
bool SygusEnumerator::TermEnumMasterFv::initialize(SygusEnumerator* se,
                                                   TypeNode tn)
{
  d_se = se;
  d_tn = tn;
  d_currSize = 0;
  Node ret = getCurrent();
  AlwaysAssert(!ret.isNull());
  SygusEnumerator::TermCache& tc = d_se->d_tcache[d_tn];
  tc.addTerm(ret);
  return true;
}

Node SygusEnumerator::TermEnumMasterFv::getCurrent()
{
  Node ret = d_se->d_tds->getFreeVar(d_tn, d_currSize);
  Trace("sygus-enum-debug2") << "master_fv(" << d_tn << "): mk " << ret
                             << std::endl;
  return ret;
}

bool SygusEnumerator::TermEnumMasterFv::increment()
{
  SygusEnumerator::TermCache& tc = d_se->d_tcache[d_tn];
  // size increments at a constant rate
  d_currSize++;
  tc.pushEnumSizeIndex();
  Node curr = getCurrent();
  Trace("sygus-enum-debug2") << "master_fv(" << d_tn << "): increment, add "
                             << curr << std::endl;
  bool ret = tc.addTerm(curr);
  AlwaysAssert(ret);
  return true;
}

}  // namespace quantifiers
}  // namespace theory
}  // namespace CVC4
