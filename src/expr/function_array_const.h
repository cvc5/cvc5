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
 * Function array constant, which is an almost constant function
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

/**
 * A function array constant is the canonical form of an almost constant
 * function. It relies on the fact that array constants have a canonical
 * form.
 */
class FunctionArrayConst
{
 public:
  /**
   * Constructor
   *
   * @param type The function type of this function array constant
   * @param avalue The array value of this function array constant
   *
   * It should be the case that avalue is a constant array. It further
   * more should be the case that if avalue has type
   *    (Array T1 (Array T2 .. (Array Tn T)))
   * then type should be
   *    (-> T1 T2 ... Tn T)
   * Note that T may itself be an array, e.g. for functions returning arrays.
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
