/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2024 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Sort type size utility. Used for model construction for higher-order.
 */

#ifndef CVC5__EXPR__SORT_TYPE_SIZE_H
#define CVC5__EXPR__SORT_TYPE_SIZE_H

#include <map>
#include <optional>
#include <vector>

#include "expr/node.h"

namespace cvc5::internal {

/**
 * This struct is used to sort terms by the "size" of their type
 *   The size of the type is the number of nodes in the type, for example
 *  size of Int is 1
 *  size of Function( Int, Int ) is 3
 *  size of Function( Function( Bool, Int ), Int ) is 5
 */
struct SortTypeSize
{
  // stores the size of the type
  std::map<TypeNode, size_t> d_type_size;
 public:
  // compares the type size of i and j
  // returns true iff the size of i is less than that of j
  // tiebreaks are determined by node value
  bool operator()(Node i, Node j);
  /** get the size of type tn */
  size_t getTypeSize(const TypeNode& tn);
};

}  // namespace cvc5::internal

#endif /* CVC5__EXPR__SORT_TYPE_SIZE_H */
