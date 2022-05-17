/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2022 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Representation of an almost constant function
 */

#include "cvc5_public.h"

#ifndef CVC5__EXPR__FUNCTION_CONST_H
#define CVC5__EXPR__FUNCTION_CONST_H

#include <iosfwd>
#include <memory>

namespace cvc5::internal {

template <bool ref_count>
class NodeTemplate;
typedef NodeTemplate<true> Node;
class TypeNode;

class FunctionConst
{
 public:
  /**
   */
  FunctionConst(const Node& value);
  ~FunctionConst();

  FunctionConst(const FunctionConst& other);
  FunctionConst& operator=(const FunctionConst& other);

  const TypeNode& getType() const;
  const Node& getValue() const;

  bool operator==(const FunctionConst& fc) const;
  bool operator!=(const FunctionConst& fc) const;
  bool operator<(const FunctionConst& fc) const;
  bool operator<=(const FunctionConst& fc) const;
  bool operator>(const FunctionConst& fc) const;
  bool operator>=(const FunctionConst& fc) const;

 private:
  /** The value */
  std::unique_ptr<Node> d_value;
};

std::ostream& operator<<(std::ostream& out, const FunctionConst& fc);

/** Hash function for the FunctionConst constants. */
struct FunctionConstHashFunction
{
  size_t operator()(const FunctionConst& fc) const;
};

}  // namespace cvc5::internal

#endif /* CVC5__EXPR__FUNCTION_CONST_H */
