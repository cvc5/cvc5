/******************************************************************************
 * Top contributors (to current version):
 *   Mikolas Janota, Andrew Reynolds, Andres Noetzli
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Implementation of an enumeration of tuples of terms for the purpose of
 * quantifier instantiation.
 */
#include "theory/quantifiers/term_tuple_enumerator.h"

#include <algorithm>
#include <functional>
#include <iterator>
#include <map>
#include <vector>

#include "base/map_util.h"
#include "base/output.h"
#include "options/quantifiers_options.h"
#include "theory/quantifiers/index_trie.h"
#include "theory/quantifiers/instantiate.h"
#include "theory/quantifiers/quant_module.h"
#include "theory/quantifiers/relevant_domain.h"
#include "theory/quantifiers/term_pools.h"
#include "theory/quantifiers/term_registry.h"
#include "theory/quantifiers/term_util.h"
#include "util/statistics_stats.h"

namespace cvc5::internal {

template <typename T>
static Cvc5ostream& operator<<(Cvc5ostream& out, const std::vector<T>& v)
{
  out << "[ ";
  std::copy(v.begin(), v.end(), std::ostream_iterator<T>(out, " "));
  return out << "]";
}

/** Tracing purposes, printing a masked vector of indices. */
static void traceMaskedVector(const char* trace,
                              const char* name,
                              const std::vector<bool>& mask,
                              const std::vector<size_t>& values)
{
  Assert(mask.size() == values.size());
  Trace(trace) << name << " [ ";
  for (size_t variableIx = 0; variableIx < mask.size(); variableIx++)
  {
    if (mask[variableIx])
    {
      Trace(trace) << values[variableIx] << " ";
    }
    else
    {
      Trace(trace) << "_ ";
    }
  }
  Trace(trace) << "]" << std::endl;
}

namespace theory {
namespace quantifiers {
/**
 * Base class for enumerators of tuples of terms for the purpose of
 * quantification instantiation. The tuples are represented as tuples of
 * indices of  terms, where the tuple has as many elements as there are
 * quantified variables in the considered quantifier.
 *
 * Like so, we see a tuple as a number, where the digits may have different
 * ranges. The most significant digits are stored first.
 *
 * Tuples are enumerated  in a lexicographic order in stages. There are 2
 * possible strategies, either  all tuples in a given stage have the same sum of
 * digits, or, the maximum  over these digits is the same.
 * */
class TermTupleEnumeratorBase : public TermTupleEnumeratorInterface
{
 public:
  /** Initialize the class with the quantifier to be instantiated. */
  TermTupleEnumeratorBase(Node quantifier, const TermTupleEnumeratorEnv* env)
      : d_quantifier(quantifier),
        d_variableCount(d_quantifier[0].getNumChildren()),
        d_env(env),
        d_stepCounter(0),
        d_disabledCombinations(
            true)  // do not record combinations with no blanks

  {
    d_changePrefix = d_variableCount;
  }

  virtual ~TermTupleEnumeratorBase() = default;

  // implementation of the TermTupleEnumeratorInterface
  virtual void init() override;
  virtual bool hasNext() override;
  virtual void next(/*out*/ std::vector<Node>& terms) override;
  virtual void failureReason(const std::vector<bool>& mask) override;
  // end of implementation of the TermTupleEnumeratorInterface

 protected:
  /** the quantifier whose variables are being instantiated */
  const Node d_quantifier;
  /** number of variables in the quantifier */
  const size_t d_variableCount;
  /** env of structures with a longer lifespan */
  const TermTupleEnumeratorEnv* const d_env;
  /** type for each variable */
  std::vector<TypeNode> d_typeCache;
  /** number of candidate terms for each variable */
  std::vector<size_t> d_termsSizes;
  /** tuple of indices of the current terms */
  std::vector<size_t> d_termIndex;
  /** total number of steps of the enumerator */
  uint32_t d_stepCounter;

  /** a data structure storing disabled combinations of terms */
  IndexTrie d_disabledCombinations;

  /** current sum/max  of digits, depending on the strategy */
  size_t d_currentStage;
  /**total number of stages*/
  size_t d_stageCount;
  /**becomes false once the enumerator runs out of options*/
  bool d_hasNext;
  /** the length of the prefix that has to be changed in the next
  combination, i.e.  the number of the most significant digits that need to be
  changed in order to escape a  useless instantiation */
  size_t d_changePrefix;
  /** Move onto the next stage */
  bool increaseStage();
  /** Move onto the next stage, sum strategy. */
  bool increaseStageSum();
  /** Move onto the next stage, max strategy. */
  bool increaseStageMax();
  /** Move on in the current stage */
  bool nextCombination();
  /** Move onto the next combination. */
  bool nextCombinationInternal();
  /** Find the next lexicographically smallest combination of terms that change
   * on the change prefix, each digit is within the current state,  and there is
   * at least one digit not in the previous stage. */
  bool nextCombinationSum();
  /** Find the next lexicographically smallest combination of terms that change
   * on the change prefix and their sum is equal to d_currentStage. */
  bool nextCombinationMax();
  /** Set up terms for given variable.  */
  virtual size_t prepareTerms(size_t variableIx) = 0;
  /** Get a given term for a given variable.  */
  CVC5_WARN_UNUSED_RESULT virtual Node getTerm(size_t variableIx,
                                               size_t term_index) = 0;
};

/**
 * Enumerate ground terms as they come from the term database.
 */
class TermTupleEnumeratorBasic : public TermTupleEnumeratorBase
{
 public:
  TermTupleEnumeratorBasic(Node quantifier,
                           const TermTupleEnumeratorEnv* env,
                           QuantifiersState& qs)
      : TermTupleEnumeratorBase(quantifier, env),
        d_qs(qs),
        d_tdb(env->d_tr->getTermDatabase())
  {
  }

  virtual ~TermTupleEnumeratorBasic() = default;

 protected:
  /**  a list of terms for each type */
  std::map<TypeNode, std::vector<Node> > d_termDbList;
  virtual size_t prepareTerms(size_t variableIx) override;
  virtual Node getTerm(size_t variableIx, size_t term_index) override;
  /** Reference to quantifiers state */
  QuantifiersState& d_qs;
  /** Pointer to term database */
  TermDb* d_tdb;
};

/**
 * Enumerate ground terms according to the relevant domain class.
 */
class TermTupleEnumeratorRD : public TermTupleEnumeratorBase
{
 public:
  TermTupleEnumeratorRD(Node quantifier,
                        const TermTupleEnumeratorEnv* env,
                        RelevantDomain* rd)
      : TermTupleEnumeratorBase(quantifier, env), d_rd(rd)
  {
  }
  virtual ~TermTupleEnumeratorRD() = default;

 protected:
  virtual size_t prepareTerms(size_t variableIx) override
  {
    return d_rd->getRDomain(d_quantifier, variableIx)->d_terms.size();
  }
  virtual Node getTerm(size_t variableIx, size_t term_index) override
  {
    return d_rd->getRDomain(d_quantifier, variableIx)->d_terms[term_index];
  }
  /** The relevant domain */
  RelevantDomain* d_rd;
};

void TermTupleEnumeratorBase::init()
{
  Trace("inst-alg-rd") << "Initializing enumeration " << d_quantifier
                       << std::endl;
  d_currentStage = 0;
  d_hasNext = true;
  d_stageCount = 1;  // in the case of full effort we do at least one stage

  if (d_variableCount == 0)
  {
    d_hasNext = false;
    return;
  }

  // prepare a sequence of terms for each quantified variable
  // additionally initialize the cache for variable types
  for (size_t variableIx = 0; variableIx < d_variableCount; variableIx++)
  {
    d_typeCache.push_back(d_quantifier[0][variableIx].getType());
    const size_t termsSize = prepareTerms(variableIx);
    Trace("inst-alg-rd") << "Variable " << variableIx << " has " << termsSize
                         << " in relevant domain." << std::endl;
    if (termsSize == 0 && !d_env->d_fullEffort)
    {
      d_hasNext = false;
      return;  // give up on an empty dommain
    }
    d_termsSizes.push_back(termsSize);
    d_stageCount = std::max(d_stageCount, termsSize);
  }

  Trace("inst-alg-rd") << "Will do " << d_stageCount
                       << " stages of instantiation." << std::endl;
  d_termIndex.resize(d_variableCount, 0);
}

bool TermTupleEnumeratorBase::hasNext()
{
  if (!d_hasNext)
  {
    return false;
  }

  if (d_stepCounter++ == 0)
  {  // TODO:any (nice)  way of avoiding this special if?
    Assert(d_currentStage == 0);
    Trace("inst-alg-rd") << "Try stage " << d_currentStage << "..."
                         << std::endl;
    return true;
  }

  // try to find the next combination
  return d_hasNext = nextCombination();
}

void TermTupleEnumeratorBase::failureReason(const std::vector<bool>& mask)
{
  if (TraceIsOn("inst-alg"))
  {
    traceMaskedVector("inst-alg", "failureReason", mask, d_termIndex);
  }
  std::vector<Node> tti;
  next(tti);
  d_disabledCombinations.add(mask, tti);  // record failure
  // update change prefix accordingly
  for (d_changePrefix = mask.size();
       d_changePrefix && !mask[d_changePrefix - 1];
       d_changePrefix--)
    ;
}

void TermTupleEnumeratorBase::next(/*out*/ std::vector<Node>& terms)
{
  Trace("inst-alg-rd") << "Try instantiation: " << d_termIndex << std::endl;
  terms.resize(d_variableCount);
  for (size_t variableIx = 0; variableIx < d_variableCount; variableIx++)
  {
    const Node t =
        d_termsSizes[variableIx] == 0
            ? d_env->d_tr->getTermForType(d_quantifier[0][variableIx].getType())
            : getTerm(variableIx, d_termIndex[variableIx]);
    terms[variableIx] = t;
    Trace("inst-alg-rd") << t << "  ";
    Assert(!t.isNull());
    Assert(t.getType() == d_quantifier[0][variableIx].getType())
        << "Bad type: " << t << " " << t.getType() << " "
        << d_quantifier[0][variableIx].getType();
  }
  Trace("inst-alg-rd") << std::endl;
}

bool TermTupleEnumeratorBase::increaseStageSum()
{
  const size_t lowerBound = d_currentStage + 1;
  Trace("inst-alg-rd") << "Try sum " << lowerBound << "..." << std::endl;
  d_currentStage = 0;
  for (size_t digit = d_termIndex.size();
       d_currentStage < lowerBound && digit--;)
  {
    const size_t missing = lowerBound - d_currentStage;
    const size_t maxValue = d_termsSizes[digit] ? d_termsSizes[digit] - 1 : 0;
    d_termIndex[digit] = std::min(missing, maxValue);
    d_currentStage += d_termIndex[digit];
  }
  return d_currentStage >= lowerBound;
}

bool TermTupleEnumeratorBase::increaseStage()
{
  d_changePrefix = d_variableCount;  // simply reset upon increase stage
  return d_env->d_increaseSum ? increaseStageSum() : increaseStageMax();
}

bool TermTupleEnumeratorBase::increaseStageMax()
{
  d_currentStage++;
  if (d_currentStage >= d_stageCount)
  {
    return false;
  }
  Trace("inst-alg-rd") << "Try stage " << d_currentStage << "..." << std::endl;
  // skipping some elements that have already been definitely seen
  // find the least significant digit that can be set to the current stage
  // TODO: should we skip all?
  std::fill(d_termIndex.begin(), d_termIndex.end(), 0);
  bool found = false;
  for (size_t digit = d_termIndex.size(); !found && digit--;)
  {
    if (d_termsSizes[digit] > d_currentStage)
    {
      found = true;
      d_termIndex[digit] = d_currentStage;
    }
  }
  Assert(found);
  return found;
}

bool TermTupleEnumeratorBase::nextCombination()
{
  while (true)
  {
    Trace("inst-alg-rd") << "changePrefix " << d_changePrefix << std::endl;
    if (!nextCombinationInternal() && !increaseStage())
    {
      return false;  // ran out of combinations
    }
    std::vector<Node> tti;
    next(tti);
    if (!d_disabledCombinations.find(tti, d_changePrefix))
    {
      return true;  // current combination vetted by disabled combinations
    }
  }
}

/** Move onto the next combination, depending on the strategy. */
bool TermTupleEnumeratorBase::nextCombinationInternal()
{
  return d_env->d_increaseSum ? nextCombinationSum() : nextCombinationMax();
}

/** Find the next lexicographically smallest combination of terms that change
 * on the change prefix and their sum is equal to d_currentStage. */
bool TermTupleEnumeratorBase::nextCombinationMax()
{
  // look for the least significant digit, within change prefix,
  // that can be increased
  bool found = false;
  size_t increaseDigit = d_changePrefix;
  while (!found && increaseDigit--)
  {
    const size_t new_value = d_termIndex[increaseDigit] + 1;
    if (new_value < d_termsSizes[increaseDigit] && new_value <= d_currentStage)
    {
      d_termIndex[increaseDigit] = new_value;
      // send everything after the increased digit to 0
      std::fill(d_termIndex.begin() + increaseDigit + 1, d_termIndex.end(), 0);
      found = true;
    }
  }
  if (!found)
  {
    return false;  // nothing to increase
  }
  // check if the combination has at least one digit in the current stage,
  // since at least one digit was increased, no need for this in stage 1
  bool inStage = d_currentStage <= 1;
  for (size_t i = increaseDigit + 1; !inStage && i--;)
  {
    inStage = d_termIndex[i] >= d_currentStage;
  }
  if (!inStage)  // look for a digit that can increase to current stage
  {
    for (increaseDigit = d_variableCount, found = false;
         !found && increaseDigit--;)
    {
      found = d_termsSizes[increaseDigit] > d_currentStage;
    }
    if (!found)
    {
      return false;  // nothing to increase to the current stage
    }
    Assert(d_termsSizes[increaseDigit] > d_currentStage
           && d_termIndex[increaseDigit] < d_currentStage);
    d_termIndex[increaseDigit] = d_currentStage;
    // send everything after the increased digit to 0
    std::fill(d_termIndex.begin() + increaseDigit + 1, d_termIndex.end(), 0);
  }
  return true;
}

/** Find the next lexicographically smallest combination of terms that change
 * on the change prefix, each digit is within the current state,  and there is
 * at least one digit not in the previous stage. */
bool TermTupleEnumeratorBase::nextCombinationSum()
{
  size_t suffixSum = 0;
  bool found = false;
  size_t increaseDigit = d_termIndex.size();
  while (increaseDigit--)
  {
    const size_t newValue = d_termIndex[increaseDigit] + 1;
    found = suffixSum > 0 && newValue < d_termsSizes[increaseDigit]
            && increaseDigit < d_changePrefix;
    if (found)
    {
      // digit can be increased and suffix can be decreased
      d_termIndex[increaseDigit] = newValue;
      break;
    }
    suffixSum += d_termIndex[increaseDigit];
    d_termIndex[increaseDigit] = 0;
  }
  if (!found)
  {
    return false;
  }
  Assert(suffixSum > 0);
  // increaseDigit went up by one, hence, distribute (suffixSum - 1) in the
  // least significant digits
  suffixSum--;
  for (size_t digit = d_termIndex.size(); suffixSum > 0 && digit--;)
  {
    const size_t maxValue = d_termsSizes[digit] ? d_termsSizes[digit] - 1 : 0;
    d_termIndex[digit] = std::min(suffixSum, maxValue);
    suffixSum -= d_termIndex[digit];
  }
  Assert(suffixSum == 0);  // everything should have been distributed
  return true;
}

size_t TermTupleEnumeratorBasic::prepareTerms(size_t variableIx)
{
  const TypeNode type_node = d_typeCache[variableIx];
  if (!ContainsKey(d_termDbList, type_node))
  {
    const size_t ground_terms_count = d_tdb->getNumTypeGroundTerms(type_node);
    std::map<Node, Node> repsFound;
    for (size_t j = 0; j < ground_terms_count; j++)
    {
      Node gt = d_tdb->getTypeGroundTerm(type_node, j);
      if (!quantifiers::TermUtil::hasInstConstAttr(gt))
      {
        Node rep = d_qs.getRepresentative(gt);
        if (repsFound.find(rep) == repsFound.end())
        {
          repsFound[rep] = gt;
          d_termDbList[type_node].push_back(gt);
        }
      }
    }
  }

  Trace("inst-alg-rd") << "Instantiation Terms for child " << variableIx << ": "
                       << d_termDbList[type_node] << std::endl;
  return d_termDbList[type_node].size();
}

Node TermTupleEnumeratorBasic::getTerm(size_t variableIx, size_t term_index)
{
  const TypeNode type_node = d_typeCache[variableIx];
  Assert(term_index < d_termDbList[type_node].size());
  return d_termDbList[type_node][term_index];
}

/**
 * Enumerate ground terms as they come from a user-provided term pool
 */
class TermTupleEnumeratorPool : public TermTupleEnumeratorBase
{
 public:
  TermTupleEnumeratorPool(Node quantifier,
                          const TermTupleEnumeratorEnv* env,
                          Node pool)
      : TermTupleEnumeratorBase(quantifier, env),
        d_pool(pool)
  {
    Assert(d_pool.getKind() == kind::INST_POOL);
  }

  virtual ~TermTupleEnumeratorPool() = default;

 protected:
  /** The pool annotation */
  Node d_pool;
  /**  a list of terms for each id */
  std::map<size_t, std::vector<Node> > d_poolList;
  /** gets the terms from the pool */
  size_t prepareTerms(size_t variableIx) override
  {
    Assert(d_pool.getNumChildren() > variableIx);
    // prepare terms from pool
    d_poolList[variableIx].clear();
    d_env->d_tr->getTermsForPool(d_pool[variableIx], d_poolList[variableIx]);
    Trace("pool-inst") << "Instantiation Terms for child " << variableIx << ": "
                       << d_poolList[variableIx] << std::endl;
    return d_poolList[variableIx].size();
  }
  Node getTerm(size_t variableIx, size_t term_index) override
  {
    Assert(term_index < d_poolList[variableIx].size());
    return d_poolList[variableIx][term_index];
  }
};

TermTupleEnumeratorInterface* mkTermTupleEnumerator(
    Node q, const TermTupleEnumeratorEnv* env, QuantifiersState& qs)
{
  return static_cast<TermTupleEnumeratorInterface*>(
      new TermTupleEnumeratorBasic(q, env, qs));
}
TermTupleEnumeratorInterface* mkTermTupleEnumeratorRd(
    Node q, const TermTupleEnumeratorEnv* env, RelevantDomain* rd)
{
  return static_cast<TermTupleEnumeratorInterface*>(
      new TermTupleEnumeratorRD(q, env, rd));
}

TermTupleEnumeratorInterface* mkTermTupleEnumeratorPool(
    Node q, const TermTupleEnumeratorEnv* env, Node pool)
{
  return static_cast<TermTupleEnumeratorInterface*>(
      new TermTupleEnumeratorPool(q, env, pool));
}

}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal
