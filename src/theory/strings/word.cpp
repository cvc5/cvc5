/*********************                                                        */
/*! \file word.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Implementation of utility functions for words.
 **/

#include "theory/strings/word.h"

#include "util/regexp.h"
#include "expr/sequence.h"

using namespace CVC4::kind;

namespace CVC4 {
namespace theory {
namespace strings {

Node Word::mkEmptyWord(TypeNode tn)
{
  if (tn.isString())
  {
    return mkEmptyWord(CONST_STRING);
  }
  else if (tn.isSequence())
  {
    std::vector<Expr> seq;
    return NodeManager::currentNM()->mkConst(ExprSequence(tn.toType(),seq));
  }
  Unimplemented();
  return Node::null();
}

Node Word::mkEmptyWord(Kind k)
{
  if (k == CONST_STRING)
  {
    std::vector<unsigned> vec;
    return NodeManager::currentNM()->mkConst(String(vec));
  }
  Unimplemented();
  return Node::null();
}

Node Word::mkWord(const std::vector<Node>& xs)
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
  else if (k==CONST_SEQUENCE)
  {
    // FIXME
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
  else if (k==CONST_SEQUENCE)
  {
    return x.getConst<ExprSequence>().getSequence().size();
  }
  Unimplemented();
  return 0;
}

bool Word::isEmpty(TNode x) { return getLength(x) == 0; }

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
  else if (k==CONST_SEQUENCE)
  {
    Assert(y.getKind() == CONST_SEQUENCE);
    const Sequence& sx = x.getConst<ExprSequence>().getSequence();
    const Sequence& sy = y.getConst<ExprSequence>().getSequence();
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
  else if (k==CONST_SEQUENCE)
  {
    Assert(y.getKind() == CONST_SEQUENCE);
    const Sequence& sx = x.getConst<ExprSequence>().getSequence();
    const Sequence& sy = y.getConst<ExprSequence>().getSequence();
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
  else if (k==CONST_SEQUENCE)
  {
    Assert(y.getKind() == CONST_SEQUENCE);
    const Sequence& sx = x.getConst<ExprSequence>().getSequence();
    const Sequence& sy = y.getConst<ExprSequence>().getSequence();
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
  else if (k==CONST_SEQUENCE)
  {
    Assert(y.getKind() == CONST_SEQUENCE);
    const Sequence& sx = x.getConst<ExprSequence>().getSequence();
    const Sequence& sy = y.getConst<ExprSequence>().getSequence();
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
  else if (k==CONST_SEQUENCE)
  {
    Assert(y.getKind() == CONST_SEQUENCE);
    const Sequence& sx = x.getConst<ExprSequence>().getSequence();
    const Sequence& sy = y.getConst<ExprSequence>().getSequence();
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
  else if (k==CONST_SEQUENCE)
  {
    Assert(y.getKind() == CONST_SEQUENCE);
    const Sequence& sx = x.getConst<ExprSequence>().getSequence();
    const Sequence& sy = y.getConst<ExprSequence>().getSequence();
    return sx.hasSuffix(sy);
  }
  Unimplemented();
  return false;
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
  else if (k==CONST_SEQUENCE)
  {
    Assert(y.getKind() == CONST_SEQUENCE);
    Assert(t.getKind() == CONST_SEQUENCE);
    const Sequence& sx = x.getConst<ExprSequence>().getSequence();
    const Sequence& sy = y.getConst<ExprSequence>().getSequence();
    const Sequence& st = t.getConst<ExprSequence>().getSequence();
    Sequence res = sx.replace(sy, st);
    return nm->mkConst(res.toExprSequence());
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
  else if (k==CONST_SEQUENCE)
  {
    const Sequence& sx = x.getConst<ExprSequence>().getSequence();
    Sequence res = sx.substr(i);
    return nm->mkConst(res.toExprSequence());
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
  else if (k==CONST_SEQUENCE)
  {
    const Sequence& sx = x.getConst<ExprSequence>().getSequence();
    Sequence res = sx.substr(i, j);
    return nm->mkConst(res.toExprSequence());
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
  else if (k==CONST_SEQUENCE)
  {
    const Sequence& sx = x.getConst<ExprSequence>().getSequence();
    Sequence res = sx.suffix(i);
    return nm->mkConst(res.toExprSequence());
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
  else if (k==CONST_SEQUENCE)
  {
    Assert(y.getKind() == CONST_SEQUENCE);
    const Sequence& sx = x.getConst<ExprSequence>().getSequence();
    const Sequence& sy = y.getConst<ExprSequence>().getSequence();
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
  else if (k==CONST_SEQUENCE)
  {
    Assert(y.getKind() == CONST_SEQUENCE);
    const Sequence& sx = x.getConst<ExprSequence>().getSequence();
    const Sequence& sy = y.getConst<ExprSequence>().getSequence();
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
  else if (k==CONST_SEQUENCE)
  {
    Assert(y.getKind() == CONST_SEQUENCE);
    const Sequence& sx = x.getConst<ExprSequence>().getSequence();
    const Sequence& sy = y.getConst<ExprSequence>().getSequence();
    return sx.roverlap(sy);
  }
  Unimplemented();
  return 0;
}

}  // namespace strings
}  // namespace theory
}  // namespace CVC4
