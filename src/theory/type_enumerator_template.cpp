/*********************                                                        */
/*! \file type_enumerator.cpp
 ** \verbatim
 ** Original author: mdeters
 ** Major contributors: none
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009-2012  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief Enumerators for types
 **
 ** Enumerators for types.
 **/

#include <sstream>

#include "theory/type_enumerator.h"

#include "expr/kind.h"
#include "util/Assert.h"

${type_enumerator_includes}
#line 28 "${template}"

using namespace std;

namespace CVC4 {
namespace theory {

TypeEnumeratorInterface* TypeEnumerator::mkTypeEnumerator(TypeNode type) throw(AssertionException) {
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
#line 49 "${template}"
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
