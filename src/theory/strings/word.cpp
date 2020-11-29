/*********************                                                        */
/*! \file word.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Andres Noetzli
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Implementation of utility functions for words.
 **/

#include "theory/strings/word.h"

#include "expr/sequence.h"
#include "util/string.h"

using namespace CVC4::kind;

namespace CVC4 {
namespace theory {
namespace strings {

Node Word::mkEmptyWord(TypeNode tn)
{
  if (tn.isString())
  {
    std::vector<unsigned> vec;
    return NodeManager::currentNM()->mkConst(String(vec));
  }
  else if (tn.isSequence())
  {
    std::vector<Node> seq;
    return NodeManager::currentNM()->mkConst(
        Sequence(tn.getSequenceElementType(), seq));
  }
  Unimplemented();
  return Node::null();
}

Node Word::mkWordFlatten(const std::vector<Node>& xs)
{
  Assert(!xs.empty());
  NodeManager* nm = NodeManager::currentNM();
  Kind k = xs[0].getKind();
  if (k == CONST_STRING)
  {
    std::vector<unsigned> vec;
    for (TNode x : xs)
    {
      Assert(x.getKind() == CONST_STRING);
      String sx = x.getConst<String>();
      const std::vector<unsigned>& vecc = sx.getVec();
      vec.insert(vec.end(), vecc.begin(), vecc.end());
    }
    return nm->mkConst(String(vec));
  }
  else if (k == CONST_SEQUENCE)
  {
    std::vector<Node> seq;
    TypeNode tn = xs[0].getType();
    for (TNode x : xs)
    {
      Assert(x.getType() == tn);
      const Sequence& sx = x.getConst<Sequence>();
      const std::vector<Node>& vecc = sx.getVec();
      seq.insert(seq.end(), vecc.begin(), vecc.end());
    }
    return NodeManager::currentNM()->mkConst(
        Sequence(tn.getSequenceElementType(), seq));
  }
  Unimplemented();
  return Node::null();
}

size_t Word::getLength(TNode x)
{
  Kind k = x.getKind();
  if (k == CONST_STRING)
  {
    return x.getConst<String>().size();
  }
  else if (k == CONST_SEQUENCE)
  {
    return x.getConst<Sequence>().size();
  }
  Unimplemented() << "Word::getLength on " << x;
  return 0;
}

std::vector<Node> Word::getChars(TNode x)
{
  Kind k = x.getKind();
  std::vector<Node> ret;
  NodeManager* nm = NodeManager::currentNM();
  if (k == CONST_STRING)
  {
    std::vector<unsigned> ccVec;
    const std::vector<unsigned>& cvec = x.getConst<String>().getVec();
    for (unsigned chVal : cvec)
    {
      ccVec.clear();
      ccVec.push_back(chVal);
      Node ch = nm->mkConst(String(ccVec));
      ret.push_back(ch);
    }
    return ret;
  }
  else if (k == CONST_SEQUENCE)
  {
    TypeNode t = x.getConst<Sequence>().getType();
    const Sequence& sx = x.getConst<Sequence>();
    const std::vector<Node>& vec = sx.getVec();
    for (const Node& v : vec)
    {
      ret.push_back(nm->mkConst(Sequence(t, {v})));
    }
    return ret;
  }
  Unimplemented();
  return ret;
}

bool Word::isEmpty(TNode x) { return x.isConst() && getLength(x) == 0; }

bool Word::strncmp(TNode x, TNode y, std::size_t n)
{
  Kind k = x.getKind();
  if (k == CONST_STRING)
  {
    Assert(y.getKind() == CONST_STRING);
    String sx = x.getConst<String>();
    String sy = y.getConst<String>();
    return sx.strncmp(sy, n);
  }
  else if (k == CONST_SEQUENCE)
  {
    Assert(y.getKind() == CONST_SEQUENCE);
    const Sequence& sx = x.getConst<Sequence>();
    const Sequence& sy = y.getConst<Sequence>();
    return sx.strncmp(sy, n);
  }
  Unimplemented();
  return false;
}

bool Word::rstrncmp(TNode x, TNode y, std::size_t n)
{
  Kind k = x.getKind();
  if (k == CONST_STRING)
  {
    Assert(y.getKind() == CONST_STRING);
    String sx = x.getConst<String>();
    String sy = y.getConst<String>();
    return sx.rstrncmp(sy, n);
  }
  else if (k == CONST_SEQUENCE)
  {
    Assert(y.getKind() == CONST_SEQUENCE);
    const Sequence& sx = x.getConst<Sequence>();
    const Sequence& sy = y.getConst<Sequence>();
    return sx.rstrncmp(sy, n);
  }
  Unimplemented();
  return false;
}

std::size_t Word::find(TNode x, TNode y, std::size_t start)
{
  Kind k = x.getKind();
  if (k == CONST_STRING)
  {
    Assert(y.getKind() == CONST_STRING);
    String sx = x.getConst<String>();
    String sy = y.getConst<String>();
    return sx.find(sy, start);
  }
  else if (k == CONST_SEQUENCE)
  {
    Assert(y.getKind() == CONST_SEQUENCE);
    const Sequence& sx = x.getConst<Sequence>();
    const Sequence& sy = y.getConst<Sequence>();
    return sx.find(sy, start);
  }
  Unimplemented();
  return 0;
}

std::size_t Word::rfind(TNode x, TNode y, std::size_t start)
{
  Kind k = x.getKind();
  if (k == CONST_STRING)
  {
    Assert(y.getKind() == CONST_STRING);
    String sx = x.getConst<String>();
    String sy = y.getConst<String>();
    return sx.rfind(sy, start);
  }
  else if (k == CONST_SEQUENCE)
  {
    Assert(y.getKind() == CONST_SEQUENCE);
    const Sequence& sx = x.getConst<Sequence>();
    const Sequence& sy = y.getConst<Sequence>();
    return sx.rfind(sy, start);
  }
  Unimplemented();
  return 0;
}

bool Word::hasPrefix(TNode x, TNode y)
{
  Kind k = x.getKind();
  if (k == CONST_STRING)
  {
    Assert(y.getKind() == CONST_STRING);
    String sx = x.getConst<String>();
    String sy = y.getConst<String>();
    return sx.hasPrefix(sy);
  }
  else if (k == CONST_SEQUENCE)
  {
    Assert(y.getKind() == CONST_SEQUENCE);
    const Sequence& sx = x.getConst<Sequence>();
    const Sequence& sy = y.getConst<Sequence>();
    return sx.hasPrefix(sy);
  }
  Unimplemented();
  return false;
}

bool Word::hasSuffix(TNode x, TNode y)
{
  Kind k = x.getKind();
  if (k == CONST_STRING)
  {
    Assert(y.getKind() == CONST_STRING);
    String sx = x.getConst<String>();
    String sy = y.getConst<String>();
    return sx.hasSuffix(sy);
  }
  else if (k == CONST_SEQUENCE)
  {
    Assert(y.getKind() == CONST_SEQUENCE);
    const Sequence& sx = x.getConst<Sequence>();
    const Sequence& sy = y.getConst<Sequence>();
    return sx.hasSuffix(sy);
  }
  Unimplemented();
  return false;
}

Node Word::update(TNode x, std::size_t i, TNode t)
{
  NodeManager* nm = NodeManager::currentNM();
  Kind k = x.getKind();
  if (k == CONST_STRING)
  {
    Assert(t.getKind() == CONST_STRING);
    String sx = x.getConst<String>();
    String st = t.getConst<String>();
    return nm->mkConst(String(sx.update(i, st)));
  }
  else if (k == CONST_SEQUENCE)
  {
    Assert(t.getKind() == CONST_SEQUENCE);
    const Sequence& sx = x.getConst<Sequence>();
    const Sequence& st = t.getConst<Sequence>();
    Sequence res = sx.update(i, st);
    return nm->mkConst(res);
  }
  Unimplemented();
  return Node::null();
}
Node Word::replace(TNode x, TNode y, TNode t)
{
  NodeManager* nm = NodeManager::currentNM();
  Kind k = x.getKind();
  if (k == CONST_STRING)
  {
    Assert(y.getKind() == CONST_STRING);
    Assert(t.getKind() == CONST_STRING);
    String sx = x.getConst<String>();
    String sy = y.getConst<String>();
    String st = t.getConst<String>();
    return nm->mkConst(String(sx.replace(sy, st)));
  }
  else if (k == CONST_SEQUENCE)
  {
    Assert(y.getKind() == CONST_SEQUENCE);
    Assert(t.getKind() == CONST_SEQUENCE);
    const Sequence& sx = x.getConst<Sequence>();
    const Sequence& sy = y.getConst<Sequence>();
    const Sequence& st = t.getConst<Sequence>();
    Sequence res = sx.replace(sy, st);
    return nm->mkConst(res);
  }
  Unimplemented();
  return Node::null();
}
Node Word::substr(TNode x, std::size_t i)
{
  NodeManager* nm = NodeManager::currentNM();
  Kind k = x.getKind();
  if (k == CONST_STRING)
  {
    String sx = x.getConst<String>();
    return nm->mkConst(String(sx.substr(i)));
  }
  else if (k == CONST_SEQUENCE)
  {
    const Sequence& sx = x.getConst<Sequence>();
    Sequence res = sx.substr(i);
    return nm->mkConst(res);
  }
  Unimplemented();
  return Node::null();
}
Node Word::substr(TNode x, std::size_t i, std::size_t j)
{
  NodeManager* nm = NodeManager::currentNM();
  Kind k = x.getKind();
  if (k == CONST_STRING)
  {
    String sx = x.getConst<String>();
    return nm->mkConst(String(sx.substr(i, j)));
  }
  else if (k == CONST_SEQUENCE)
  {
    const Sequence& sx = x.getConst<Sequence>();
    Sequence res = sx.substr(i, j);
    return nm->mkConst(res);
  }
  Unimplemented();
  return Node::null();
}

Node Word::prefix(TNode x, std::size_t i) { return substr(x, 0, i); }

Node Word::suffix(TNode x, std::size_t i)
{
  NodeManager* nm = NodeManager::currentNM();
  Kind k = x.getKind();
  if (k == CONST_STRING)
  {
    String sx = x.getConst<String>();
    return nm->mkConst(String(sx.suffix(i)));
  }
  else if (k == CONST_SEQUENCE)
  {
    const Sequence& sx = x.getConst<Sequence>();
    Sequence res = sx.suffix(i);
    return nm->mkConst(res);
  }
  Unimplemented();
  return Node::null();
}

bool Word::noOverlapWith(TNode x, TNode y)
{
  Kind k = x.getKind();
  if (k == CONST_STRING)
  {
    Assert(y.getKind() == CONST_STRING);
    String sx = x.getConst<String>();
    String sy = y.getConst<String>();
    return sx.noOverlapWith(sy);
  }
  else if (k == CONST_SEQUENCE)
  {
    Assert(y.getKind() == CONST_SEQUENCE);
    const Sequence& sx = x.getConst<Sequence>();
    const Sequence& sy = y.getConst<Sequence>();
    return sx.noOverlapWith(sy);
  }
  Unimplemented();
  return false;
}

std::size_t Word::overlap(TNode x, TNode y)
{
  Kind k = x.getKind();
  if (k == CONST_STRING)
  {
    Assert(y.getKind() == CONST_STRING);
    String sx = x.getConst<String>();
    String sy = y.getConst<String>();
    return sx.overlap(sy);
  }
  else if (k == CONST_SEQUENCE)
  {
    Assert(y.getKind() == CONST_SEQUENCE);
    const Sequence& sx = x.getConst<Sequence>();
    const Sequence& sy = y.getConst<Sequence>();
    return sx.overlap(sy);
  }
  Unimplemented();
  return 0;
}

std::size_t Word::roverlap(TNode x, TNode y)
{
  Kind k = x.getKind();
  if (k == CONST_STRING)
  {
    Assert(y.getKind() == CONST_STRING);
    String sx = x.getConst<String>();
    String sy = y.getConst<String>();
    return sx.roverlap(sy);
  }
  else if (k == CONST_SEQUENCE)
  {
    Assert(y.getKind() == CONST_SEQUENCE);
    const Sequence& sx = x.getConst<Sequence>();
    const Sequence& sy = y.getConst<Sequence>();
    return sx.roverlap(sy);
  }
  Unimplemented();
  return 0;
}

bool Word::isRepeated(TNode x)
{
  Kind k = x.getKind();
  if (k == CONST_STRING)
  {
    return x.getConst<String>().isRepeated();
  }
  else if (k == CONST_SEQUENCE)
  {
    return x.getConst<Sequence>().isRepeated();
  }
  Unimplemented();
  return false;
}

Node Word::splitConstant(TNode x, TNode y, size_t& index, bool isRev)
{
  Assert(x.isConst() && y.isConst());
  size_t lenA = getLength(x);
  size_t lenB = getLength(y);
  index = lenA <= lenB ? 1 : 0;
  size_t lenShort = index == 1 ? lenA : lenB;
  bool cmp = isRev ? rstrncmp(x, y, lenShort) : strncmp(x, y, lenShort);
  if (cmp)
  {
    Node l = index == 0 ? x : y;
    if (isRev)
    {
      size_t new_len = getLength(l) - lenShort;
      return substr(l, 0, new_len);
    }
    else
    {
      return substr(l, lenShort);
    }
  }
  // not the same prefix/suffix
  return Node::null();
}

Node Word::reverse(TNode x)
{
  NodeManager* nm = NodeManager::currentNM();
  Kind k = x.getKind();
  if (k == CONST_STRING)
  {
    String sx = x.getConst<String>();
    std::vector<unsigned> nvec = sx.getVec();
    std::reverse(nvec.begin(), nvec.end());
    return nm->mkConst(String(nvec));
  }
  else if (k == CONST_SEQUENCE)
  {
    const Sequence& sx = x.getConst<Sequence>();
    const std::vector<Node>& vecc = sx.getVec();
    std::vector<Node> vecr(vecc.begin(), vecc.end());
    std::reverse(vecr.begin(), vecr.end());
    Sequence res(sx.getType(), vecr);
    return nm->mkConst(res);
  }
  Unimplemented();
  return Node::null();
}

}  // namespace strings
}  // namespace theory
}  // namespace CVC4
