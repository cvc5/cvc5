/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Aina Niemetz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2024 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Implementation of enumerator for regular expressions.
 */

#include "theory/strings/regexp_enumerator.h"

namespace cvc5::internal {
namespace theory {
namespace strings {

RegExpEnumerator::RegExpEnumerator(TypeNode type, TypeEnumeratorProperties* tep)
    : TypeEnumeratorBase<RegExpEnumerator>(type),
      d_senum(NodeManager::currentNM()->stringType(), tep)
{
}

RegExpEnumerator::RegExpEnumerator(const RegExpEnumerator& enumerator)
    : TypeEnumeratorBase<RegExpEnumerator>(enumerator.getType()),
      d_senum(enumerator.d_senum)
{
}

Node RegExpEnumerator::operator*()
{
  NodeManager* nm = NodeManager::currentNM();
  return nm->mkNode(Kind::STRING_TO_REGEXP, *d_senum);
}

RegExpEnumerator& RegExpEnumerator::operator++()
{
  ++d_senum;
  return *this;
}

bool RegExpEnumerator::isFinished() { return d_senum.isFinished(); }

}  // namespace strings
}  // namespace theory
}  // namespace cvc5::internal
