/******************************************************************************
 * Top contributors (to current version):
 *   Tim King, Aina Niemetz, Clark Barrett
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Simplifications for ITE expressions.
 *
 * This module implements preprocessing phases designed to simplify ITE
 * expressions.  Based on:
 * Kim, Somenzi, Jin.  Efficient Term-ITE Conversion for SMT.  FMCAD 2009.
 * Burch, Jerry.  Techniques for Verifying Superscalar Microprocessors.  DAC
 *'96
 */

#include "cvc5_private.h"

#ifndef CVC5__ITE_UTILITIES_H
#define CVC5__ITE_UTILITIES_H

#include <unordered_map>
#include <vector>

#include "expr/node.h"
#include "smt/env_obj.h"
#include "util/hash.h"
#include "util/statistics_stats.h"

namespace cvc5::internal {

namespace preprocessing {

class AssertionPipeline;

namespace util {

class ITECompressor;
class ITESimplifier;
class ITECareSimplifier;

/**
 * A caching visitor that computes whether a node contains a term ite.
 */
class ContainsTermITEVisitor
{
 public:
  ContainsTermITEVisitor();
  ~ContainsTermITEVisitor();

  /** returns true if a node contains a term ite. */
  bool containsTermITE(TNode n);

  /** Garbage collects the cache. */
  void garbageCollect();

  /** returns the size of the cache. */
  size_t cache_size() const { return d_cache.size(); }

 private:
  typedef std::unordered_map<Node, bool> NodeBoolMap;
  NodeBoolMap d_cache;
};

class ITEUtilities : protected EnvObj
{
 public:
  ITEUtilities(Env& env);
  ~ITEUtilities();

  Node simpITE(TNode assertion);

  bool simpIteDidALotOfWorkHeuristic() const;

  /* returns false if an assertion is discovered to be equal to false. */
  bool compress(AssertionPipeline* assertionsToPreprocess);

  Node simplifyWithCare(TNode e);

  void clear();

  ContainsTermITEVisitor* getContainsVisitor()
  {
    return d_containsVisitor.get();
  }

  bool containsTermITE(TNode n)
  {
    return d_containsVisitor->containsTermITE(n);
  }

 private:
  std::unique_ptr<ContainsTermITEVisitor> d_containsVisitor;
  ITECompressor* d_compressor;
  ITESimplifier* d_simplifier;
  ITECareSimplifier* d_careSimp;
};

class IncomingArcCounter
{
 public:
  IncomingArcCounter(bool skipVars = false, bool skipConstants = false);
  ~IncomingArcCounter();
  void computeReachability(const std::vector<Node>& assertions);

  inline uint32_t lookupIncoming(Node n) const
  {
    NodeCountMap::const_iterator it = d_reachCount.find(n);
    if (it == d_reachCount.end())
    {
      return 0;
    }
    else
    {
      return (*it).second;
    }
  }
  void clear();

 private:
  typedef std::unordered_map<Node, uint32_t> NodeCountMap;
  NodeCountMap d_reachCount;

  bool d_skipVariables;
  bool d_skipConstants;
};

class TermITEHeightCounter
{
 public:
  TermITEHeightCounter();
  ~TermITEHeightCounter();

  /**
   * Compute and [potentially] cache the termITEHeight() of e.
   * The term ite height equals the maximum number of term ites
   * encountered on any path from e to a leaf.
   * Inductively:
   *  - termITEHeight(leaves) = 0
   *  - termITEHeight(e: term-ite(c, t, e) ) =
   *     1 + max(termITEHeight(t), termITEHeight(e)) ; Don't include c
   *  - termITEHeight(e not term ite) = max_{c in children(e))
   * (termITEHeight(c))
   */
  uint32_t termITEHeight(TNode e);

  /** Clear the cache. */
  void clear();

  /** Size of the cache. */
  size_t cache_size() const;

 private:
  typedef std::unordered_map<Node, uint32_t> NodeCountMap;
  NodeCountMap d_termITEHeight;
}; /* class TermITEHeightCounter */

/**
 * A routine designed to undo the potentially large blow up
 * due to expansion caused by the ite simplifier.
 */
class ITECompressor : protected EnvObj
{
 public:
  ITECompressor(Env& env, ContainsTermITEVisitor* contains);
  ~ITECompressor();

  /* returns false if an assertion is discovered to be equal to false. */
  bool compress(AssertionPipeline* assertionsToPreprocess);

  /* garbage Collects the compressor. */
  void garbageCollect();

 private:
  class Statistics
  {
   public:
    IntStat d_compressCalls;
    IntStat d_skolemsAdded;
    Statistics(StatisticsRegistry& reg);
  };

  void reset();

  Node push_back_boolean(Node original, Node compressed);
  bool multipleParents(TNode c);
  Node compressBooleanITEs(Node toCompress);
  Node compressTerm(Node toCompress);
  Node compressBoolean(Node toCompress);

  Node d_true;  /* Copy of true. */
  Node d_false; /* Copy of false. */

  ContainsTermITEVisitor* d_contains;
  AssertionPipeline* d_assertions;
  IncomingArcCounter d_incoming;

  typedef std::unordered_map<Node, Node> NodeMap;
  NodeMap d_compressed;

  Statistics d_statistics;
}; /* class ITECompressor */

class ITESimplifier : protected EnvObj
{
 public:
  ITESimplifier(Env& env, ContainsTermITEVisitor* d_containsVisitor);
  ~ITESimplifier();

  Node simpITE(TNode assertion);

  bool doneALotOfWorkHeuristic() const;
  void clearSimpITECaches();

 private:
  using NodeVec = std::vector<Node>;
  using ConstantLeavesMap = std::unordered_map<Node, NodeVec*>;
  using NodePair = std::pair<Node, Node>;
  using NodePairHashFunction =
      PairHashFunction<Node, Node, std::hash<Node>, std::hash<Node>>;
  using NodePairMap = std::unordered_map<NodePair, Node, NodePairHashFunction>;

  class Statistics
  {
   public:
    IntStat d_maxNonConstantsFolded;
    IntStat d_unexpected;
    IntStat d_unsimplified;
    IntStat d_exactMatchFold;
    IntStat d_binaryPredFold;
    IntStat d_specialEqualityFolds;
    IntStat d_simpITEVisits;

    HistogramStat<uint32_t> d_inSmaller;

    Statistics(StatisticsRegistry& reg);
  };

  inline bool containsTermITE(TNode n)
  {
    return d_containsVisitor->containsTermITE(n);
  }

  inline uint32_t termITEHeight(TNode e)
  {
    return d_termITEHeight.termITEHeight(e);
  }

  // d_constantLeaves satisfies the following invariants:
  // not containsTermITE(x) then !isKey(x)
  // containsTermITE(x):
  // - not isKey(x) then this value is uncomputed
  // - d_constantLeaves[x] == NULL, then this contains a non-constant leaf
  // - d_constantLeaves[x] != NULL, then this contains a sorted list of constant
  // leaf
  bool isConstantIte(TNode e);

  /** If its not a constant and containsTermITE(ite),
   * returns a sorted NodeVec of the leaves. */
  NodeVec* computeConstantLeaves(TNode ite);

  /* transforms */
  Node transformAtom(TNode atom);
  Node attemptConstantRemoval(TNode atom);
  Node attemptLiftEquality(TNode atom);
  Node attemptEagerRemoval(TNode atom);

  // Given ConstantIte trees lcite and rcite,
  // return a boolean expression equivalent to (= lcite rcite)
  Node intersectConstantIte(TNode lcite, TNode rcite);

  // Given ConstantIte tree cite and a constant c,
  // return a boolean expression equivalent to (= lcite c)
  Node constantIteEqualsConstant(TNode cite, TNode c);

  Node replaceOver(Node n, Node replaceWith, Node simpVar);
  Node replaceOverTermIte(Node term, Node simpAtom, Node simpVar);

  bool leavesAreConst(TNode e, theory::TheoryId tid);
  bool leavesAreConst(TNode e);

  Node simpConstants(TNode simpContext, TNode iteNode, TNode simpVar);

  Node createSimpContext(TNode c, Node& iteNode, Node& simpVar);

  Node d_true;
  Node d_false;

  ContainsTermITEVisitor* d_containsVisitor;

  TermITEHeightCounter d_termITEHeight;

  // ConstantIte is a small inductive sublanguage:
  //     constant
  // or  termITE(cnd, ConstantIte, ConstantIte)
  ConstantLeavesMap d_constantLeaves;

  // Lists all of the vectors in d_constantLeaves for fast deletion.
  std::vector<NodeVec*> d_allocatedConstantLeaves;

  uint32_t d_citeEqConstApplications;

  NodePairMap d_constantIteEqualsConstantCache;
  NodePairMap d_replaceOverCache;
  NodePairMap d_replaceOverTermIteCache;

  std::unordered_map<Node, bool> d_leavesConstCache;

  NodePairMap d_simpConstCache;
  std::unordered_map<TypeNode, Node> d_simpVars;
  Node getSimpVar(TypeNode t);

  typedef std::unordered_map<Node, Node> NodeMap;
  NodeMap d_simpContextCache;

  NodeMap d_simpITECache;
  Node simpITEAtom(TNode atom);

  Statistics d_statistics;
};

class ITECareSimplifier
{
 public:
  ITECareSimplifier();
  ~ITECareSimplifier();

  Node simplifyWithCare(TNode e);

  void clear();

 private:
  /**
   * This should always equal the number of care sets allocated by
   * this object - the number of these that have been deleted. This is
   * initially 0 and should always be 0 at the *start* of
   * ~ITECareSimplifier().
   */
  unsigned d_careSetsOutstanding;

  Node d_true;
  Node d_false;

  typedef std::unordered_map<TNode, Node> TNodeMap;

  class CareSetPtr;
  class CareSetPtrVal
  {
   public:
    bool safeToGarbageCollect() const { return d_refCount == 0; }

   private:
    friend class ITECareSimplifier::CareSetPtr;
    ITECareSimplifier& d_iteSimplifier;
    unsigned d_refCount;
    std::set<Node> d_careSet;
    CareSetPtrVal(ITECareSimplifier& simp)
        : d_iteSimplifier(simp), d_refCount(1)
    {
    }
  }; /* class ITECareSimplifier::CareSetPtrVal */

  std::vector<CareSetPtrVal*> d_usedSets;
  void careSetPtrGC(CareSetPtrVal* val) { d_usedSets.push_back(val); }

  class CareSetPtr
  {
    CareSetPtrVal* d_val;
    CareSetPtr(CareSetPtrVal* val) : d_val(val) {}

   public:
    CareSetPtr() : d_val(NULL) {}
    CareSetPtr(const CareSetPtr& cs)
    {
      d_val = cs.d_val;
      if (d_val != NULL)
      {
        ++(d_val->d_refCount);
      }
    }
    ~CareSetPtr()
    {
      if (d_val != NULL && (--(d_val->d_refCount) == 0))
      {
        d_val->d_iteSimplifier.careSetPtrGC(d_val);
      }
    }
    CareSetPtr& operator=(const CareSetPtr& cs)
    {
      if (d_val != cs.d_val)
      {
        if (d_val != NULL && (--(d_val->d_refCount) == 0))
        {
          d_val->d_iteSimplifier.careSetPtrGC(d_val);
        }
        d_val = cs.d_val;
        if (d_val != NULL)
        {
          ++(d_val->d_refCount);
        }
      }
      return *this;
    }
    std::set<Node>& getCareSet() { return d_val->d_careSet; }

    static CareSetPtr mkNew(ITECareSimplifier& simp);
    static CareSetPtr recycle(CareSetPtrVal* val)
    {
      Assert(val != NULL && val->d_refCount == 0);
      val->d_refCount = 1;
      return CareSetPtr(val);
    }
  }; /* class ITECareSimplifier::CareSetPtr */

  CareSetPtr getNewSet();

  typedef std::map<TNode, CareSetPtr> CareMap;
  void updateQueue(CareMap& queue, TNode e, CareSetPtr& careSet);
  Node substitute(TNode e, TNodeMap& substTable, TNodeMap& cache);
};

}  // namespace util
}  // namespace preprocessing
}  // namespace cvc5::internal

#endif
