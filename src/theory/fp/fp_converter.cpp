/*********************                                                        */
/*! \file fp_converter.cpp
 ** \verbatim
 ** Original author: Martin Brain
 ** Major contributors: 
 ** Minor contributors (to current version): 
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2014  University of Oxford
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief [[ Conversion of floating-point operations to bit-vectors using symfpu. ]]
 **
 **/


#include "theory/fp/fp_converter.h"

#include <stack>


namespace CVC4 {
namespace theory {
namespace fp {


  size_t PairTypeNodeHashFunction::operator()(const std::pair<TypeNode, TypeNode> &p) const {
    TypeNodeHashFunction h;
    return h(p.first) ^ h(p.second);
  }

  

  fpConverter::fpConverter (context::UserContext* user) :
    additionalAssertions(user)
  {
  }


  Node fpConverter::convert (TNode node) {
    Unimplemented("Conversion not implemented.");
    return node;
  }


  Node fpConverter::getValue (Valuation &val, TNode var) {
    Unimplemented("Conversion not implemented.");
    return Node::null();
  }


}/* CVC4::theory::fp namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */
