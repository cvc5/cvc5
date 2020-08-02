/*********************                                                        */
/*! \file type_enumerator.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Mathias Preiner, Tim King
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Implementation of enumerators for strings
 **/

#include "theory/strings/type_enumerator.h"

#include "theory/strings/theory_strings_utils.h"
#include "util/string.h"

namespace CVC4 {
namespace theory {
namespace strings {

Node makeStandardModelConstant(const std::vector<unsigned>& vec,
                               uint32_t cardinality)
{
  std::vector<unsigned> mvec;
  // if we contain all of the printable characters
  if (cardinality >= 255)
  {
    for (unsigned i = 0, vsize = vec.size(); i < vsize; i++)
    {
      unsigned curr = vec[i];
      // convert
      Assert(vec[i] < cardinality);
      if (vec[i] <= 61)
      {
        // first 62 printable characters [\u{65}-\u{126}]: 'A', 'B', 'C', ...
        curr = vec[i] + 65;
      }
      else if (vec[i] <= 94)
      {
        // remaining 33 printable characters [\u{32}-\u{64}]: ' ', '!', '"', ...
        curr = vec[i] - 30;
      }
      else
      {
        // the remaining characters, starting with \u{127} and wrapping around
        // the first 32 non-printable characters.
        curr = (vec[i] + 32) % cardinality;
      }
      mvec.push_back(curr);
    }
  }
  else
  {
    mvec = vec;
  }
  return NodeManager::currentNM()->mkConst(String(mvec));
}

WordIter::WordIter(uint32_t startLength) : d_hasEndLength(false), d_endLength(0)
{
  for (uint32_t i = 0; i < startLength; i++)
  {
    d_data.push_back(0);
  }
}
WordIter::WordIter(uint32_t startLength, uint32_t endLength)
    : d_hasEndLength(true), d_endLength(endLength)
{
  for (uint32_t i = 0; i < startLength; i++)
  {
    d_data.push_back(0);
  }
}

WordIter::WordIter(const WordIter& witer)
    : d_hasEndLength(witer.d_hasEndLength),
      d_endLength(witer.d_endLength),
      d_data(witer.d_data)
{
}

const std::vector<unsigned>& WordIter::getData() const { return d_data; }

bool WordIter::increment(uint32_t card)
{
  for (unsigned i = 0, dsize = d_data.size(); i < dsize; ++i)
  {
    if (d_data[i] + 1 < card)
    {
      ++d_data[i];
      return true;
    }
    else
    {
      d_data[i] = 0;
    }
  }
  if (d_hasEndLength && d_data.size() == d_endLength)
  {
    return false;
  }
  // otherwise increase length
  d_data.push_back(0);
  return true;
}

SEnumLen::SEnumLen(TypeNode tn, uint32_t startLength)
    : d_type(tn), d_witer(new WordIter(startLength))
{
}
SEnumLen::SEnumLen(TypeNode tn, uint32_t startLength, uint32_t endLength)
    : d_type(tn), d_witer(new WordIter(startLength, endLength))
{
}

SEnumLen::SEnumLen(const SEnumLen& e)
    : d_type(e.d_type), d_witer(new WordIter(*e.d_witer)), d_curr(e.d_curr)
{
}

Node SEnumLen::getCurrent() const { return d_curr; }

bool SEnumLen::isFinished() const { return d_curr.isNull(); }

StringEnumLen::StringEnumLen(uint32_t startLength,
                             uint32_t endLength,
                             uint32_t card)
    : SEnumLen(NodeManager::currentNM()->stringType(), startLength, endLength),
      d_cardinality(card)
{
  mkCurr();
}

StringEnumLen::StringEnumLen(uint32_t startLength, uint32_t card)
    : SEnumLen(NodeManager::currentNM()->stringType(), startLength),
      d_cardinality(card)
{
  mkCurr();
}

bool StringEnumLen::increment()
{
  // always use the same cardinality
  if (!d_witer->increment(d_cardinality))
  {
    d_curr = Node::null();
    return false;
  }
  mkCurr();
  return true;
}

void StringEnumLen::mkCurr()
{
  d_curr = makeStandardModelConstant(d_witer->getData(), d_cardinality);
}

SeqEnumLen::SeqEnumLen(TypeNode tn,
                       TypeEnumeratorProperties* tep,
                       uint32_t startLength)
    : SEnumLen(tn, startLength)
{
  d_elementEnumerator.reset(
      new TypeEnumerator(d_type.getSequenceElementType(), tep));
  mkCurr();
}

SeqEnumLen::SeqEnumLen(TypeNode tn,
                       TypeEnumeratorProperties* tep,
                       uint32_t startLength,
                       uint32_t endLength)
    : SEnumLen(tn, startLength, endLength)
{
  d_elementEnumerator.reset(
      new TypeEnumerator(d_type.getSequenceElementType(), tep));
  // ensure non-empty element domain
  d_elementDomain.push_back((**d_elementEnumerator).toExpr());
  ++(*d_elementEnumerator);
  mkCurr();
}

SeqEnumLen::SeqEnumLen(const SeqEnumLen& wenum)
    : SEnumLen(wenum),
      d_elementEnumerator(new TypeEnumerator(*wenum.d_elementEnumerator)),
      d_elementDomain(wenum.d_elementDomain)
{
}

bool SeqEnumLen::increment()
{
  if (!d_elementEnumerator->isFinished())
  {
    // yet to establish domain
    Assert(d_elementEnumerator != nullptr);
    d_elementDomain.push_back((**d_elementEnumerator).toExpr());
    ++(*d_elementEnumerator);
  }
  // the current cardinality is the domain size of the element
  if (!d_witer->increment(d_elementDomain.size()))
  {
    Assert(d_elementEnumerator->isFinished());
    d_curr = Node::null();
    return false;
  }
  mkCurr();
  return true;
}

void SeqEnumLen::mkCurr()
{
  std::vector<Node> seq;
  const std::vector<unsigned>& data = d_witer->getData();
  for (unsigned i : data)
  {
    Assert(i < d_elementDomain.size());
    seq.push_back(d_elementDomain[i]);
  }
  // make sequence from seq
  d_curr = NodeManager::currentNM()->mkConst(
      Sequence(d_type.getSequenceElementType(), seq));
}

StringEnumerator::StringEnumerator(TypeNode type, TypeEnumeratorProperties* tep)
    : TypeEnumeratorBase<StringEnumerator>(type),
      d_wenum(0, utils::getAlphabetCardinality())
{
  Assert(type.getKind() == kind::TYPE_CONSTANT
         && type.getConst<TypeConstant>() == STRING_TYPE);
}

StringEnumerator::StringEnumerator(const StringEnumerator& enumerator)
    : TypeEnumeratorBase<StringEnumerator>(enumerator.getType()),
      d_wenum(enumerator.d_wenum)
{
}

Node StringEnumerator::operator*() { return d_wenum.getCurrent(); }

StringEnumerator& StringEnumerator::operator++()
{
  d_wenum.increment();
  return *this;
}

bool StringEnumerator::isFinished() { return d_wenum.isFinished(); }

SequenceEnumerator::SequenceEnumerator(TypeNode type,
                                       TypeEnumeratorProperties* tep)
    : TypeEnumeratorBase<SequenceEnumerator>(type), d_wenum(type, tep, 0)
{
}

SequenceEnumerator::SequenceEnumerator(const SequenceEnumerator& enumerator)
    : TypeEnumeratorBase<SequenceEnumerator>(enumerator.getType()),
      d_wenum(enumerator.d_wenum)
{
}

Node SequenceEnumerator::operator*() { return d_wenum.getCurrent(); }

SequenceEnumerator& SequenceEnumerator::operator++()
{
  d_wenum.increment();
  return *this;
}

bool SequenceEnumerator::isFinished() { return d_wenum.isFinished(); }

}  // namespace strings
}  // namespace theory
}  // namespace CVC4
