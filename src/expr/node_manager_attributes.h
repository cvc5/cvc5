/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Morgan Deters
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * [[ Add one-line brief description here ]]
 *
 * [[ Add lengthier description here ]]
 * \todo document this file
 */

#pragma once

#include "expr/attribute.h"

namespace cvc5::internal {
namespace expr {

// Definition of an attribute for the variable name.
namespace attr {
  struct VarNameTag { };
  struct SortArityTag { };
  struct TypeTag { };
  struct TypeCheckedTag { };
  struct UnresolvedDatatypeTag
  {
  };
  struct TupleDatatypeTag
  {
  };
  struct DatatypeIndexTag
  {
  };
  struct OracleIndexTag
  {
  };
  }  // namespace attr

typedef Attribute<attr::VarNameTag, std::string> VarNameAttr;
typedef Attribute<attr::SortArityTag, uint64_t> SortArityAttr;
typedef expr::Attribute<expr::attr::TypeTag, TypeNode> TypeAttr;
typedef expr::Attribute<expr::attr::TypeCheckedTag, bool> TypeCheckedAttr;

/** Attribute is true for unresolved datatype sorts */
using UnresolvedDatatypeAttr =
    expr::Attribute<expr::attr::UnresolvedDatatypeTag, bool>;

/** Mapping tuples to their datatype type encoding */
using TupleDatatypeAttr =
    expr::Attribute<expr::attr::TupleDatatypeTag, TypeNode>;

/** Mapping datatype types to the index of their datatype in node manager */
using DatatypeIndexAttr = Attribute<attr::DatatypeIndexTag, uint64_t>;

/** Mapping oracle constant nodes to the index of their oracle in the node
 * manager */
using OracleIndexAttr = expr::Attribute<expr::attr::OracleIndexTag, uint64_t>;

}  // namespace expr
}  // namespace cvc5::internal
