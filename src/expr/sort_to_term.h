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
 * Payload that represents a sort to be represented as a term.
 */

#include "cvc5_public.h"

#ifndef CVC5__EXPR__SORT_TO_TERM_H
#define CVC5__EXPR__SORT_TO_TERM_H

#include <iosfwd>
#include <memory>

namespace cvc5::internal {

class TypeNode;

class SortToTerm
{
 public:
  /**
   * Constructs an emptyset of the specified type. Note that the argument
   * is the type of the set itself, NOT the type of the elements.
   */
  SortToTerm(const TypeNode& setType);
  SortToTerm(const SortToTerm& other);
  ~SortToTerm();

  /** Get the type that this sort-to-term represents */
  const TypeNode& getType() const;

 private:
  SortToTerm();
  /** The type */
  std::unique_ptr<TypeNode> d_type;
};

std::ostream& operator<<(std::ostream& out, const SortToTerm& es);

struct SortToTermHashFunction
{
  size_t operator()(const SortToTerm& es) const;
};

}  // namespace cvc5::internal

#endif /* CVC5__EXPR__SORT_TO_TERM_H */
