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
 * Representation of bound variables in codatatype values
 */

#include "cvc5_public.h"

#ifndef CVC5__EXPR__CODATATYPE_BOUND_VARIABLE_H
#define CVC5__EXPR__CODATATYPE_BOUND_VARIABLE_H

#include <iosfwd>
#include <memory>

#include "util/integer.h"

namespace cvc5::internal {

class TypeNode;

/**
 * In theory, codatatype values are represented in using a MU-notation form,
 * where recursive values may contain free constants indexed by their de Bruijn
 * indices. This is sometimes written:
 *    MU x. (cons 0 x).
 * where the MU binder is label for a term position, which x references.
 * Instead of constructing an explicit MU binder (which is problematic for
 * canonicity), we use de Bruijn indices for representing bound variables,
 * whose index indicates the level in which it is nested. For example, we
 * represent the above value as:
 *    (cons 0 @cbv_0)
 * In the above value, @cbv_0 is a pointer to its direct parent, so the above
 * value represents the infinite list (cons 0 (cons 0 (cons 0 ... ))).
 * Another example, the value:
 *    (cons 0 (cons 1 @cbv_1))
 * @cbv_1 is pointer to the top most node of this value, so this is value
 * represents the infinite list (cons 0 (cons 1 (cons 0 (cons 1 ...)))). The
 * value:
 *    (cons 0 (cons 1 @cbv_0))
 * on the other hand represents the lasso:
 *    (cons 0 (cons 1 (cons 1 (cons 1 ... ))))
 *
 * This class is used for representing the indexed bound variables in the above
 * values. It is considered a constant (isConst is true). However, constants
 * of codatatype type are normalized by the rewriter (see datatypes rewriter
 * normalizeCodatatypeConstant) to ensure their canonicity, via a variant
 * of Hopcroft's algorithm.
 */
class CodatatypeBoundVariable
{
 public:
  CodatatypeBoundVariable(const TypeNode& type, Integer index);
  ~CodatatypeBoundVariable();

  CodatatypeBoundVariable(const CodatatypeBoundVariable& other);

  const TypeNode& getType() const;
  const Integer& getIndex() const;
  bool operator==(const CodatatypeBoundVariable& cbv) const;
  bool operator!=(const CodatatypeBoundVariable& cbv) const;
  bool operator<(const CodatatypeBoundVariable& cbv) const;
  bool operator<=(const CodatatypeBoundVariable& cbv) const;
  bool operator>(const CodatatypeBoundVariable& cbv) const;
  bool operator>=(const CodatatypeBoundVariable& cbv) const;

 private:
  std::unique_ptr<TypeNode> d_type;
  const Integer d_index;
};
std::ostream& operator<<(std::ostream& out, const CodatatypeBoundVariable& cbv);

/**
 * Hash function for codatatype bound variables.
 */
struct CodatatypeBoundVariableHashFunction
{
  size_t operator()(const CodatatypeBoundVariable& cbv) const;
};

}  // namespace cvc5::internal

#endif /* CVC5__UNINTERPRETED_CONSTANT_H */
