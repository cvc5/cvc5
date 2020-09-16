/*********************                                                        */
/*! \file type_enumerator_template.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Morgan Deters, Mathias Preiner, Tim King
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Enumerators for types
 **
 ** Enumerators for types.
 **/

#include <sstream>

#include "base/check.h"
#include "expr/kind.h"
#include "theory/type_enumerator.h"


${type_enumerator_includes}

using namespace std;

namespace CVC4 {
namespace theory {

TypeEnumeratorInterface* TypeEnumerator::mkTypeEnumerator(
    TypeNode type, TypeEnumeratorProperties* tep)
{
  switch (type.getKind())
  {
    case kind::TYPE_CONSTANT:
      switch (type.getConst<TypeConstant>())
      {
        ${mk_type_enumerator_type_constant_cases}
        default: Unhandled() << "No type enumerator for type `" << type << "'";
      }
      Unreachable();
      ${mk_type_enumerator_cases}
    default: Unhandled() << "No type enumerator for type `" << type << "'";
  }
  Unreachable();
}

}/* CVC4::theory namespace */
}/* CVC4 namespace */
