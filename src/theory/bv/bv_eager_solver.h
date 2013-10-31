/*********************                                                        */
/*! \file bv_eager_solver.h
 ** \verbatim
 ** Original author: Liana Hadarean 
 ** Major contributors: none
 ** Minor contributors (to current version): 
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2013  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief Eager bit-blasting solver. 
 **
 ** Eager bit-blasting solver.
 **/

#include "cvc4_private.h"
#include "expr/node.h"
#include <vector>
#pragma once


namespace CVC4 {
namespace theory {
namespace bv {

class EagerBitblaster;

/**
 * BitblastSolver
 */
class EagerBitblastSolver {
  /** Bitblaster */
  EagerBitblaster* d_bitblaster;
  std::vector<Node> d_assertionList; 
public:
  EagerBitblastSolver(); 
  ~EagerBitblastSolver();
  bool checkSat();
  void assertFormula(Node formula); 
};

}
}
}
