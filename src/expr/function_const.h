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

class FunctionConstant
{
 public:
  /**
   */
  FunctionConstant(const Node& avalue);
  ~FunctionConstant();

  FunctionConstant(const FunctionConstant& other);
  FunctionConstant& operator=(const FunctionConstant& other);

  const TypeNode& getType() const;
  const Node& getArrayValue() const;

  bool operator==(const FunctionConstant& fc) const;
  bool operator!=(const FunctionConstant& fc) const;
  bool operator<(const FunctionConstant& fc) const;
  bool operator<=(const FunctionConstant& fc) const;
  bool operator>(const FunctionConstant& fc) const;
  bool operator>=(const FunctionConstant& fc) const;

 private:
  /** The value, which has type (Array T1 (Array T2 .. (Array Tn T))) */
  std::unique_ptr<Node> d_avalue;
  /** The (function) type (-> T1 T2 ... Tn T) */
  std::unique_ptr<TypeNode> d_type;
};

// std::ostream& operator<<(std::ostream& out, const FunctionConstant& fc);

/** Hash function for the FunctionConstant constants. */
struct FunctionConstantHashFunction
{
  size_t operator()(const FunctionConstant& fc) const;
};

}  // namespace cvc5::internal

#endif /* CVC5__EXPR__FUNCTION_CONST_H */
