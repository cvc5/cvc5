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

#ifndef CVC5__EXPR__FUNCTION_ARRAY_CONST_H
#define CVC5__EXPR__FUNCTION_ARRAY_CONST_H

#include <iosfwd>
#include <memory>

namespace cvc5::internal {

template <bool ref_count>
class NodeTemplate;
typedef NodeTemplate<true> Node;
class TypeNode;

class FunctionArrayConst
{
 public:
  /**
   */
  FunctionArrayConst(const TypeNode& type, const Node& avalue);
  ~FunctionArrayConst();

  FunctionArrayConst(const FunctionArrayConst& other);
  FunctionArrayConst& operator=(const FunctionArrayConst& other);

  const TypeNode& getType() const;
  const Node& getArrayValue() const;

  bool operator==(const FunctionArrayConst& fc) const;
  bool operator!=(const FunctionArrayConst& fc) const;
  bool operator<(const FunctionArrayConst& fc) const;
  bool operator<=(const FunctionArrayConst& fc) const;
  bool operator>(const FunctionArrayConst& fc) const;
  bool operator>=(const FunctionArrayConst& fc) const;

 private:
  /** The (function) type (-> T1 T2 ... Tn T) */
  std::unique_ptr<TypeNode> d_type;
  /** The value, which has type (Array T1 (Array T2 .. (Array Tn T))) */
  std::unique_ptr<Node> d_avalue;
};

std::ostream& operator<<(std::ostream& out, const FunctionArrayConst& fc);

/** Hash function for the FunctionArrayConst constants. */
struct FunctionArrayConstHashFunction
{
  size_t operator()(const FunctionArrayConst& fc) const;
};

}  // namespace cvc5::internal

#endif /* CVC5__EXPR__FUNCTION_ARRAY_CONST_H */
