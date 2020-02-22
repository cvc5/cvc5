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
 ** \brief Util functions for words.
 **/

#include "theory/strings/word.h"

#include "util/regexp.h"

using namespace CVC4::kind;

namespace CVC4 {
namespace theory {
namespace strings {
namespace word {

Node mkEmptyWord(TypeNode tn)
{
  if (tn.isString())
  {
    return nm->mkConst(String(""));
  }
  Assert(false);
  return Node::null();
}

Node mkWord(const std::vector<Node>& xs)
{
  Assert( !consts.empty());
  TypeNode tn = xs[0].getType();
  if (tn.isString())
  {
    return 
  }
  Assert(false);
  return Node::null();
}
  
size_t getLength(TNode x)
{
  TypeNode tn = x.getType();
  if (tn.isString())
  {
    return 
  }
  Assert(false);
  return 0;
}

bool isEmpty(TNode x)
{
  TypeNode tn = x.getType();
  if (tn.isString())
  {
    return 
  }
  Assert(false);
  return 0;
}

std::size_t find(TNode x, TNode y, std::size_t start)
{
  TypeNode tn = x.getType();
  if (tn.isString())
  {
    return 
  }
  Assert(false);
  return 0;
}

std::size_t rfind(TNode x, TNode y, std::size_t start)
{
  TypeNode tn = x.getType();
  if (tn.isString())
  {
    return 
  }
  Assert(false);
  return 0;
}

bool hasPrefix(TNode x, TNode y)
{
  TypeNode tn = x.getType();
  if (tn.isString())
  {
    return 
  }
  Assert(false);
  return false;
}

bool hasSuffix(TNode x, TNode y)
{
  TypeNode tn = x.getType();
  if (tn.isString())
  {
    return 
  }
  Assert(false);
  return false;
}

Node replace(TNode x, TNode y, Node t)
{
  TypeNode tn = x.getType();
  if (tn.isString())
  {
    return 
  }
  Assert(false);
  return Node::null();
}
Node substr(TNode x,std::size_t i)
{
  TypeNode tn = x.getType();
  if (tn.isString())
  {
    return 
  }
  Assert(false);
  return Node::null();
}
Node substr(TNode x,std::size_t i, std::size_t j)
{
  TypeNode tn = x.getType();
  if (tn.isString())
  {
    return 
  }
  Assert(false);
  return Node::null();
}

Node prefix(TNode x, std::size_t i) { 
  return substr(x,0,i);
}
Node suffix(TNode x, std::size_t i) 
{ 
  return substr(x, size() - i, i);
}

bool noOverlapWith(TNode x, TNode y)
{
  TypeNode tn = x.getType();
  if (tn.isString())
  {
    return 
  }
  Assert(false);
  return false;
}

std::size_t overlap(TNode x, TNode y)
{
  TypeNode tn = x.getType();
  if (tn.isString())
  {
    return 
  }
  Assert(false);
  return 0;
}

std::size_t roverlap(TNode x, TNode y)
{
  TypeNode tn = x.getType();
  if (tn.isString())
  {
    return 
  }
  Assert(false);
  return 0;
}
  
}  // namespace word
}  // namespace strings
}  // namespace theory
}  // namespace CVC4
