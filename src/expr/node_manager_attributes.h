/******************************************************************************
 * Top contributors (to current version):
 *   Morgan Deters
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
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

namespace cvc5 {
namespace expr {

// Definition of an attribute for the variable name.
// TODO: hide this attribute behind a NodeManager interface.
namespace attr {
  struct VarNameTag { };
  struct SortArityTag { };
  struct TypeTag { };
  struct TypeCheckedTag { };
  }  // namespace attr

typedef Attribute<attr::VarNameTag, std::string> VarNameAttr;
typedef Attribute<attr::SortArityTag, uint64_t> SortArityAttr;
typedef expr::Attribute<expr::attr::TypeTag, TypeNode> TypeAttr;
typedef expr::Attribute<expr::attr::TypeCheckedTag, bool> TypeCheckedAttr;

}  // namespace expr
}  // namespace cvc5
