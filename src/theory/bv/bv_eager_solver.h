/*********************                                                        */
/*! \file bv_eager_solver.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Liana Hadarean, Tim King
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2016 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Eager bit-blasting solver. 
 **
 ** Eager bit-blasting solver.
 **/

#include "cvc4_private.h"
#include "expr/node.h"
#include "theory/theory_model.h"
#include "theory/bv/theory_bv.h"
#include <vector>
#pragma once


namespace CVC4 {
namespace theory {
namespace bv {

class EagerBitblaster;
class AigBitblaster;

/**
 * BitblastSolver
 */
class EagerBitblastSolver {
  typedef __gnu_cxx::hash_set<TNode, TNodeHashFunction> AssertionSet;
  AssertionSet d_assertionSet;
  /** Bitblasters */
  EagerBitblaster* d_bitblaster;
  AigBitblaster* d_aigBitblaster;
  bool d_useAig;

  TheoryBV* d_bv; 
  BitVectorProof * d_bvp;

public:
  EagerBitblastSolver(theory::bv::TheoryBV* bv);
  ~EagerBitblastSolver();
  bool checkSat();
  void assertFormula(TNode formula);
  // purely for debugging purposes
  bool hasAssertions(const std::vector<TNode> &formulas);

  void turnOffAig();
  bool isInitialized();
  void initialize();
  void collectModelInfo(theory::TheoryModel* m, bool fullModel);
  void setProofLog( BitVectorProof * bvp );
};

}
}
}
