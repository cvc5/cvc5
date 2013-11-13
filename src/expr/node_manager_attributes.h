/*********************                                                        */
/*! \file node_manager_attributes.h
 ** \verbatim
 ** Original author: Morgan Deters
 ** Major contributors: none
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2013  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
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
  struct DatatypeTupleTag { };
  struct DatatypeRecordTag { };
  struct TypeTag { };
  struct TypeCheckedTag { };
}/* CVC4::expr::attr namespace */

typedef Attribute<attr::VarNameTag, std::string> VarNameAttr;
typedef Attribute<attr::GlobalVarTag(), bool> GlobalVarAttr;
typedef Attribute<attr::SortArityTag, uint64_t> SortArityAttr;
/** Attribute true for datatype types that are replacements for tuple types */
typedef expr::Attribute<expr::attr::DatatypeTupleTag, TypeNode> DatatypeTupleAttr;
/** Attribute true for datatype types that are replacements for record types */
typedef expr::Attribute<expr::attr::DatatypeRecordTag, TypeNode> DatatypeRecordAttr;
typedef expr::Attribute<expr::attr::TypeTag, TypeNode> TypeAttr;
typedef expr::Attribute<expr::attr::TypeCheckedTag, bool> TypeCheckedAttr;

}/* CVC4::expr namespace */
}/* CVC4 namespace */
