/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Andres Noetzli
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2024 by the authors listed in the file AUTHORS
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

/**
 * Sort-to-term utility, which is used to represent sorts as a term. Example
 * use cases of this include passing sorts to the arguments of skolems (e.g.
 * the n^th shared selector of a given datatype and selector type), or for
 * representing SMT-LIB version 3 terms, where sorts and terms can be freely
 * mixed.
 */
class SortToTerm
{
 public:
  /**
   * Constructs an object representing a term corresponding to the specified
   * type.
   */
  SortToTerm(const TypeNode& sort);
  SortToTerm(const SortToTerm& other);
  ~SortToTerm();

  /** Get the type that this sort-to-term represents */
  const TypeNode& getType() const;
  /** True if equal */
  bool operator==(const SortToTerm& stt) const;

 private:
  SortToTerm();
  /** The type the constant represents */
  std::unique_ptr<TypeNode> d_type;
};

std::ostream& operator<<(std::ostream& out, const SortToTerm& stt);

struct SortToTermHashFunction
{
  size_t operator()(const SortToTerm& stt) const;
};

}  // namespace cvc5::internal

#endif /* CVC5__EXPR__SORT_TO_TERM_H */
