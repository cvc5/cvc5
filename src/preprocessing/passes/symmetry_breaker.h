/*********************                                                        */
/*! \file symmetry_breaker.h
 ** \verbatim
 ** Top contributors (to current version):
 **  Paul Meng, Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2018 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Symmetry breaker for theories
 **/


#ifndef __CVC4__PREPROCESSING_PASSES_SYMMETRY_BREAKER_H_
#define __CVC4__PREPROCESSING_PASSES_SYMMETRY_BREAKER_H_

#include <map>
#include <string>
#include <vector>
#include "expr/node.h"

namespace CVC4 {
namespace preprocessing {
namespace passes {

class SymmetryBreaker{
 public:
  /**
   * Constructor
   * */
  SymmetryBreaker()
  {
    d_trueNode = NodeManager::currentNM()->mkConst<bool>(true);
    d_falseNode = NodeManager::currentNM()->mkConst<bool>(false);
  }

  /**
   * Destructor
   * */
  ~SymmetryBreaker() {}

  /**
   * This is to generate symmetry breaking constraints for partitions in parts.
   * The symmetry breaking constraints SB returned by this function conjuncted
   * with the original assertions SB ^ C is equisatisfiable to the C.
   *
   * */
  Node generateSymBkConstraints(std::vector< std::vector< Node > >& parts);

 private:

  /** True and false constant nodes */
  Node d_trueNode;
  Node d_falseNode;

  /**
   * Get the order kind for node depending on the type of node
   * */
  Kind getOrderKind(Node node);

};

}  // namespace passes
}  // namespace preprocessing
}  // namespace CVC4



#endif /* __CVC4_PREPROCESSING_PASSES_SYMMETRY_BREAKER_H_ */
