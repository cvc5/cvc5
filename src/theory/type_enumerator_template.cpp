/*********************                                                        */
/*! \file type_enumerator_template.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Morgan Deters, Paul Meng, Tim King
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2017 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Enumerators for types
 **
 ** Enumerators for types.
 **/

#include <sstream>

#include "base/cvc4_assert.h"
#include "expr/kind.h"
#include "theory/type_enumerator.h"


${type_enumerator_includes}
#line 26 "${template}"

using namespace std;

namespace CVC4 {
namespace theory {

TypeEnumeratorInterface* TypeEnumerator::mkTypeEnumerator(
    TypeNode type, TypeEnumeratorProperties* tep)
{
  switch(type.getKind()) {
  case kind::TYPE_CONSTANT:
    switch(type.getConst<TypeConstant>()) {
${mk_type_enumerator_type_constant_cases}
    default:
      {
        stringstream ss;
        ss << "No type enumerator for type `" << type << "'";
        Unhandled(ss.str());
      }
    }
    Unreachable();
${mk_type_enumerator_cases}
#line 47 "${template}"
  default:
    {
      stringstream ss;
      ss << "No type enumerator for type `" << type << "'";
      Unhandled(ss.str());
    }
  }
  Unreachable();
}

}/* CVC4::theory namespace */
}/* CVC4 namespace */
