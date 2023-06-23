/******************************************************************************
 * Top contributors (to current version):
 *   Aina Niemetz, Clark Barrett, Morgan Deters
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * An enumerator for arrays.
 */
#include "theory/arrays/type_enumerator.h"

#include "expr/array_store_all.h"
#include "expr/kind.h"
#include "expr/type_node.h"
#include "theory/arrays/theory_arrays_rewriter.h"
#include "theory/rewriter.h"
#include "theory/type_enumerator.h"

namespace cvc5::internal {
namespace theory {
namespace arrays {

ArrayEnumerator::ArrayEnumerator(TypeNode type, TypeEnumeratorProperties* tep)
    : TypeEnumeratorBase<ArrayEnumerator>(type),
      d_tep(tep),
      d_index(type.getArrayIndexType(), tep),
      d_constituentType(type.getArrayConstituentType()),
      d_nm(NodeManager::currentNM()),
      d_indexVec(),
      d_constituentVec(),
      d_finished(false),
      d_arrayConst()
{
  d_indexVec.push_back(*d_index);
  d_constituentVec.push_back(new TypeEnumerator(d_constituentType, d_tep));
  d_arrayConst =
      d_nm->mkConst(ArrayStoreAll(type, (*(*d_constituentVec.back()))));
  Trace("array-type-enum") << "Array const : " << d_arrayConst << std::endl;
}

ArrayEnumerator::ArrayEnumerator(const ArrayEnumerator& ae)
    : TypeEnumeratorBase<ArrayEnumerator>(
        ae.d_nm->mkArrayType(ae.d_index.getType(), ae.d_constituentType)),
      d_tep(ae.d_tep),
      d_index(ae.d_index),
      d_constituentType(ae.d_constituentType),
      d_nm(ae.d_nm),
      d_indexVec(ae.d_indexVec),
      d_constituentVec(),  // copied below
      d_finished(ae.d_finished),
      d_arrayConst(ae.d_arrayConst)
{
  for (std::vector<TypeEnumerator*>::const_iterator
           i = ae.d_constituentVec.begin(),
           i_end = ae.d_constituentVec.end();
       i != i_end;
       ++i)
  {
    d_constituentVec.push_back(new TypeEnumerator(**i));
  }
}

ArrayEnumerator::~ArrayEnumerator()
{
  while (!d_constituentVec.empty())
  {
    delete d_constituentVec.back();
    d_constituentVec.pop_back();
  }
}

Node ArrayEnumerator::operator*()
{
  if (d_finished)
  {
    throw NoMoreValuesException(getType());
  }
  Node n = d_arrayConst;
  for (size_t i = 0, size = d_indexVec.size(); i < size; ++i)
  {
    n = d_nm->mkNode(kind::STORE,
                     n,
                     d_indexVec[d_indexVec.size() - 1 - i],
                     *(*(d_constituentVec[i])));
    // Normalize the constant. We must do this every iteration of this loop,
    // since this utility requires all children of n to be constant, which
    // implies the first argument to STORE on the next iteration must be
    // normalized.
    n = TheoryArraysRewriter::normalizeConstant(n);
  }
  Trace("array-type-enum") << "operator * returning: " << n << std::endl;
  return n;
}

ArrayEnumerator& ArrayEnumerator::operator++()
{
  Trace("array-type-enum") << "operator++ called, **this = " << **this
                           << std::endl;

  if (d_finished)
  {
    Trace("array-type-enum") << "operator++ finished!" << std::endl;
    return *this;
  }
  while (!d_constituentVec.empty())
  {
    ++(*d_constituentVec.back());
    if (d_constituentVec.back()->isFinished())
    {
      delete d_constituentVec.back();
      d_constituentVec.pop_back();
    }
    else
    {
      break;
    }
  }

  if (d_constituentVec.empty())
  {
    ++d_index;
    if (d_index.isFinished())
    {
      Trace("array-type-enum") << "operator++ finished!" << std::endl;
      d_finished = true;
      return *this;
    }
    d_indexVec.push_back(*d_index);
    d_constituentVec.push_back(new TypeEnumerator(d_constituentType, d_tep));
    ++(*d_constituentVec.back());
    if (d_constituentVec.back()->isFinished())
    {
      Trace("array-type-enum") << "operator++ finished!" << std::endl;
      d_finished = true;
      return *this;
    }
  }

  while (d_constituentVec.size() < d_indexVec.size())
  {
    d_constituentVec.push_back(new TypeEnumerator(d_constituentType, d_tep));
  }

  Trace("array-type-enum") << "operator++ returning, **this = " << **this
                           << std::endl;
  return *this;
}

bool ArrayEnumerator::isFinished()
{
  Trace("array-type-enum") << "isFinished returning: " << d_finished
                           << std::endl;
  return d_finished;
}

}  // namespace arrays
}  // namespace theory
}  // namespace cvc5::internal
