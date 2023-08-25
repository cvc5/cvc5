/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Enumerators for regular expressions.
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__STRINGS__REGEXP_ENUMERATOR_H
#define CVC5__THEORY__STRINGS__REGEXP_ENUMERATOR_H

#include <vector>

#include "expr/node.h"
#include "expr/type_node.h"
#include "theory/strings/type_enumerator.h"

namespace cvc5::internal {
namespace theory {
namespace strings {

/**
 * Simple regular expression enumerator, generates only singleton language
 * regular expressions from a string enumeration, in other words:
 *   (str.to_re s1) ... (str.to_re sn) ....
 * where s1 ... sn ... is the enumeration for strings.
 */
class RegExpEnumerator : public TypeEnumeratorBase<RegExpEnumerator>
{
 public:
  RegExpEnumerator(TypeNode type, TypeEnumeratorProperties* tep = nullptr);
  RegExpEnumerator(const RegExpEnumerator& enumerator);
  ~RegExpEnumerator() {}
  /** get the current term */
  Node operator*() override;
  /** increment */
  RegExpEnumerator& operator++() override;
  /** is this enumerator finished? */
  bool isFinished() override;

 private:
  /** underlying string enumerator */
  StringEnumerator d_senum;
};

}  // namespace strings
}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5__THEORY__STRINGS__TYPE_ENUMERATOR_H */
