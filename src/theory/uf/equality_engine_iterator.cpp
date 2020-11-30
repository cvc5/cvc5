/*********************                                                        */
/*! \file equality_engine_iterator.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Dejan Jovanovic, Morgan Deters
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Implementation of iterator class for equality engine
 **/

#include "theory/uf/equality_engine_iterator.h"

#include "theory/uf/equality_engine.h"

namespace CVC4 {
namespace theory {
namespace eq {

EqClassesIterator::EqClassesIterator() : d_ee(nullptr), d_it(0) {}

EqClassesIterator::EqClassesIterator(const eq::EqualityEngine* ee) : d_ee(ee)
{
  Assert(d_ee->consistent());
  d_it = 0;
  // Go to the first non-internal node that is it's own representative
  if (d_it < d_ee->d_nodesCount
      && (d_ee->d_isInternal[d_it]
          || d_ee->getEqualityNode(d_it).getFind() != d_it))
  {
    ++d_it;
  }
}

Node EqClassesIterator::operator*() const { return d_ee->d_nodes[d_it]; }

bool EqClassesIterator::operator==(const EqClassesIterator& i) const
{
  return d_ee == i.d_ee && d_it == i.d_it;
}

bool EqClassesIterator::operator!=(const EqClassesIterator& i) const
{
  return !(*this == i);
}

EqClassesIterator& EqClassesIterator::operator++()
{
  ++d_it;
  while (d_it < d_ee->d_nodesCount
         && (d_ee->d_isInternal[d_it]
             || d_ee->getEqualityNode(d_it).getFind() != d_it))
  {
    ++d_it;
  }
  return *this;
}

EqClassesIterator EqClassesIterator::operator++(int)
{
  EqClassesIterator i = *this;
  ++*this;
  return i;
}

bool EqClassesIterator::isFinished() const
{
  return d_it >= d_ee->d_nodesCount;
}

EqClassIterator::EqClassIterator()
    : d_ee(nullptr), d_start(null_id), d_current(null_id)
{
}

EqClassIterator::EqClassIterator(Node eqc, const eq::EqualityEngine* ee)
    : d_ee(ee)
{
  Assert(d_ee->consistent());
  d_current = d_start = d_ee->getNodeId(eqc);
  Assert(d_start == d_ee->getEqualityNode(d_start).getFind());
  Assert(!d_ee->d_isInternal[d_start]);
}

Node EqClassIterator::operator*() const { return d_ee->d_nodes[d_current]; }

bool EqClassIterator::operator==(const EqClassIterator& i) const
{
  return d_ee == i.d_ee && d_current == i.d_current;
}

bool EqClassIterator::operator!=(const EqClassIterator& i) const
{
  return !(*this == i);
}

EqClassIterator& EqClassIterator::operator++()
{
  Assert(!isFinished());

  Assert(d_start == d_ee->getEqualityNode(d_current).getFind());
  Assert(!d_ee->d_isInternal[d_current]);

  // Find the next one
  do
  {
    d_current = d_ee->getEqualityNode(d_current).getNext();
  } while (d_ee->d_isInternal[d_current]);

  Assert(d_start == d_ee->getEqualityNode(d_current).getFind());
  Assert(!d_ee->d_isInternal[d_current]);

  if (d_current == d_start)
  {
    // we end when we have cycled back to the original representative
    d_current = null_id;
  }
  return *this;
}

EqClassIterator EqClassIterator::operator++(int)
{
  EqClassIterator i = *this;
  ++*this;
  return i;
}

bool EqClassIterator::isFinished() const { return d_current == null_id; }

}  // namespace eq
}  // Namespace theory
}  // Namespace CVC4
