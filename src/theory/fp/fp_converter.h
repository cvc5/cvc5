/*********************                                                        */
/*! \file fp_convert.h
 ** \verbatim
 ** Original author: Martin Brain
 ** Major contributors:
 ** Minor contributors (to current version):
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2014  University of Oxford
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief [[ Converts floating-point nodes to bit-vector expressions. ]]
 **
 ** [[ Uses the symfpu library to convert from floating-point operations
 **    to bit-vectors and propositions allowing the theory to be solved by
 **    'bit-blasting'. ]]
 **/

#include "theory/valuation.h"

#include "context/cdhashmap.h"
#include "context/cdlist.h"

#include "util/floatingpoint.h"


#ifndef __CVC4__THEORY__FP__FP_CONVERTER_H
#define __CVC4__THEORY__FP__FP_CONVERTER_H


namespace CVC4 {
namespace theory {
namespace fp {

  struct PairTypeNodeHashFunction {
    size_t operator()(const std::pair<TypeNode, TypeNode> &p) const;
  };


  class fpConverter {
  public :
    context::CDList<Node> additionalAssertions;

    fpConverter (context::UserContext*);

    /** Adds a node to the conversion, returns the converted node */
    Node convert (TNode);

    /** Gives the node representing the value of a given variable */
    Node getValue (Valuation &, TNode);

  };


}/* CVC4::theory::fp namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */

#endif /* __CVC4__THEORY__FP__THEORY_FP_H */
