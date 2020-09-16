/*********************                                                        */
/*! \file node_manager_attributes.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Morgan Deters, Kshitij Bansal
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief [[ Add one-line brief description here ]]
 **
 ** [[ Add lengthier description here ]]
 ** \todo document this file
 **/

#pragma once

#include "expr/attribute.h"

namespace CVC4 {
namespace expr {

// Definition of an attribute for the variable name.
// TODO: hide this attribute behind a NodeManager interface.
namespace attr {
  struct VarNameTag { };
  struct GlobalVarTag { };
  struct SortArityTag { };
  struct TypeTag { };
  struct TypeCheckedTag { };
}/* CVC4::expr::attr namespace */

typedef Attribute<attr::VarNameTag, std::string> VarNameAttr;
typedef Attribute<attr::GlobalVarTag(), bool> GlobalVarAttr;
typedef Attribute<attr::SortArityTag, uint64_t> SortArityAttr;
typedef expr::Attribute<expr::attr::TypeTag, TypeNode> TypeAttr;
typedef expr::Attribute<expr::attr::TypeCheckedTag, bool> TypeCheckedAttr;

}/* CVC4::expr namespace */
}/* CVC4 namespace */
