/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Andres Noetzli, Mathias Preiner
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Implementation of the sequence data type.
 */

#include "expr/sequence.h"

#include <limits>
#include <sstream>
#include <vector>

#include "expr/node.h"
#include "expr/type_node.h"

using namespace std;

namespace cvc5::internal {

Sequence::Sequence(const TypeNode& t, const std::vector<Node>& s)
    : d_type(new TypeNode(t)), d_seq(s)
{
}

Sequence::Sequence(const Sequence& seq)
    : d_type(new TypeNode(seq.getType())), d_seq(seq.getVec())
{
}

Sequence::~Sequence() {}

Sequence& Sequence::operator=(const Sequence& y)
{
  if (this != &y)
  {
    d_type.reset(new TypeNode(y.getType()));
    d_seq = y.getVec();
  }
  return *this;
}

int Sequence::cmp(const Sequence& y) const
{
  if (getType() != y.getType())
  {
    return getType() < y.getType() ? -1 : 1;
  }
  if (size() != y.size())
  {
    return size() < y.size() ? -1 : 1;
  }
  for (size_t i = 0, sz = size(); i < sz; ++i)
  {
    if (nth(i) != y.nth(i))
    {
      return nth(i) < y.nth(i) ? -1 : 1;
    }
  }
  return 0;
}

Sequence Sequence::concat(const Sequence& other) const
{
  Assert(getType() == other.getType());
  std::vector<Node> ret_vec(d_seq);
  ret_vec.insert(ret_vec.end(), other.d_seq.begin(), other.d_seq.end());
  return Sequence(getType(), ret_vec);
}

bool Sequence::strncmp(const Sequence& y, size_t n) const
{
  Assert(getType() == y.getType());
  size_t b = (size() >= y.size()) ? size() : y.size();
  size_t s = (size() <= y.size()) ? size() : y.size();
  if (n > s)
  {
    if (b != s)
    {
      return false;
    }
    n = s;
  }
  for (size_t i = 0; i < n; ++i)
  {
    if (nth(i) != y.nth(i))
    {
      return false;
    }
  }
  return true;
}

bool Sequence::rstrncmp(const Sequence& y, size_t n) const
{
  Assert(getType() == y.getType());
  size_t b = (size() >= y.size()) ? size() : y.size();
  size_t s = (size() <= y.size()) ? size() : y.size();
  if (n > s)
  {
    if (b != s)
    {
      return false;
    }
    n = s;
  }
  for (size_t i = 0; i < n; ++i)
  {
    if (nth(size() - i - 1) != y.nth(y.size() - i - 1))
    {
      return false;
    }
  }
  return true;
}

bool Sequence::empty() const { return d_seq.empty(); }

size_t Sequence::size() const { return d_seq.size(); }

const Node& Sequence::front() const
{
  Assert(!d_seq.empty());
  return d_seq.front();
}

const Node& Sequence::back() const
{
  Assert(!d_seq.empty());
  return d_seq.back();
}

const Node& Sequence::nth(size_t i) const
{
  Assert(i < size());
  return d_seq[i];
}

size_t Sequence::overlap(const Sequence& y) const
{
  Assert(getType() == y.getType());
  size_t i = size() < y.size() ? size() : y.size();
  for (; i > 0; i--)
  {
    Sequence s = suffix(i);
    Sequence p = y.prefix(i);
    if (s == p)
    {
      return i;
    }
  }
  return i;
}

size_t Sequence::roverlap(const Sequence& y) const
{
  Assert(getType() == y.getType());
  size_t i = size() < y.size() ? size() : y.size();
  for (; i > 0; i--)
  {
    Sequence s = prefix(i);
    Sequence p = y.suffix(i);
    if (s == p)
    {
      return i;
    }
  }
  return i;
}

const TypeNode& Sequence::getType() const { return *d_type; }

const std::vector<Node>& Sequence::getVec() const { return d_seq; }

bool Sequence::isRepeated() const
{
  if (size() > 1)
  {
    Node f = nth(0);
    for (unsigned i = 1, sz = size(); i < sz; ++i)
    {
      if (f != nth(i))
      {
        return false;
      }
    }
  }
  return true;
}

size_t Sequence::find(const Sequence& y, size_t start) const
{
  Assert(getType() == y.getType());
  if (size() < y.size() + start)
  {
    return std::string::npos;
  }
  if (y.empty())
  {
    return start;
  }
  if (empty())
  {
    return std::string::npos;
  }
  std::vector<Node>::const_iterator itr = std::search(
      d_seq.begin() + start, d_seq.end(), y.d_seq.begin(), y.d_seq.end());
  if (itr != d_seq.end())
  {
    return itr - d_seq.begin();
  }
  return std::string::npos;
}

size_t Sequence::rfind(const Sequence& y, size_t start) const
{
  Assert(getType() == y.getType());
  if (size() < y.size() + start)
  {
    return std::string::npos;
  }
  if (y.empty())
  {
    return start;
  }
  if (empty())
  {
    return std::string::npos;
  }
  std::vector<Node>::const_reverse_iterator itr = std::search(
      d_seq.rbegin() + start, d_seq.rend(), y.d_seq.rbegin(), y.d_seq.rend());
  if (itr != d_seq.rend())
  {
    return itr - d_seq.rbegin();
  }
  return std::string::npos;
}

bool Sequence::hasPrefix(const Sequence& y) const
{
  Assert(getType() == y.getType());
  size_t s = size();
  size_t ys = y.size();
  if (ys > s)
  {
    return false;
  }
  for (size_t i = 0; i < ys; i++)
  {
    if (nth(i) != y.nth(i))
    {
      return false;
    }
  }
  return true;
}

bool Sequence::hasSuffix(const Sequence& y) const
{
  Assert(getType() == y.getType());
  size_t s = size();
  size_t ys = y.size();
  if (ys > s)
  {
    return false;
  }
  size_t idiff = s - ys;
  for (size_t i = 0; i < ys; i++)
  {
    if (nth(i + idiff) != y.nth(i))
    {
      return false;
    }
  }
  return true;
}

Sequence Sequence::update(size_t i, const Sequence& t) const
{
  Assert(getType() == t.getType());
  if (i < size())
  {
    std::vector<Node> vec(d_seq.begin(), d_seq.begin() + i);
    size_t remNum = size() - i;
    size_t tnum = t.d_seq.size();
    if (tnum >= remNum)
    {
      vec.insert(vec.end(), t.d_seq.begin(), t.d_seq.begin() + remNum);
    }
    else
    {
      vec.insert(vec.end(), t.d_seq.begin(), t.d_seq.end());
      vec.insert(vec.end(), d_seq.begin() + i + tnum, d_seq.end());
    }
    return Sequence(getType(), vec);
  }
  return *this;
}

Sequence Sequence::replace(const Sequence& s, const Sequence& t) const
{
  Assert(getType() == s.getType());
  Assert(getType() == t.getType());
  size_t ret = find(s);
  if (ret != std::string::npos)
  {
    std::vector<Node> vec;
    vec.insert(vec.begin(), d_seq.begin(), d_seq.begin() + ret);
    vec.insert(vec.end(), t.d_seq.begin(), t.d_seq.end());
    vec.insert(vec.end(), d_seq.begin() + ret + s.size(), d_seq.end());
    return Sequence(getType(), vec);
  }
  return *this;
}

Sequence Sequence::substr(size_t i) const
{
  Assert(i >= 0);
  Assert(i <= size());
  std::vector<Node> retVec(d_seq.begin() + i, d_seq.end());
  return Sequence(getType(), retVec);
}

Sequence Sequence::substr(size_t i, size_t j) const
{
  Assert(i >= 0);
  Assert(j >= 0);
  Assert(i + j <= size());
  std::vector<Node>::const_iterator itr = d_seq.begin() + i;
  std::vector<Node> retVec(itr, itr + j);
  return Sequence(getType(), retVec);
}

bool Sequence::noOverlapWith(const Sequence& y) const
{
  Assert(getType() == y.getType());
  return y.find(*this) == std::string::npos
         && this->find(y) == std::string::npos && this->overlap(y) == 0
         && y.overlap(*this) == 0;
}

size_t Sequence::maxSize() { return std::numeric_limits<uint32_t>::max(); }

std::ostream& operator<<(std::ostream& os, const Sequence& s)
{
  const std::vector<Node>& vec = s.getVec();
  std::stringstream ss;
  if (vec.empty())
  {
    ss << "(as seq.empty " << s.getType() << ")";
  }
  else
  {
    ss << "(seq.++";
    for (const Node& n : vec)
    {
      ss << " " << n;
    }
    ss << ")";
  }
  return os << ss.str();
}

size_t SequenceHashFunction::operator()(const Sequence& s) const
{
  uint64_t ret = fnv1a::offsetBasis;
  const std::vector<Node>& vec = s.getVec();
  for (const Node& n : vec)
  {
    ret = fnv1a::fnv1a_64(ret, std::hash<Node>()(n));
  }
  return static_cast<size_t>(ret);
}

}  // namespace cvc5::internal
