/*********************                                                        */
/*! \file bv_bitblast_mode.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Liana Hadarean, Tim King
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2016 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Bitblasting modes for bit-vector solver.
 **
 ** Bitblasting modes for bit-vector solver.
 **/

#include "cvc4_private.h"

#ifndef __CVC4__THEORY__BV__BITBLAST_MODE_H
#define __CVC4__THEORY__BV__BITBLAST_MODE_H

#include <iosfwd>

namespace CVC4 {
namespace theory {
namespace bv {

/** Enumeration of bit-blasting modes */
enum BitblastMode {

  /**
   * Lazy bit-blasting that separates boolean reasoning
   * from term reasoning.
   */
  BITBLAST_MODE_LAZY,

  /**
   * Bit-blast eagerly to the bit-vector SAT solver.
   */
  BITBLAST_MODE_EAGER
};/* enum BitblastMode */

/** Enumeration of bit-vector equality slicer mode */
enum BvSlicerMode {

  /**
   * Force the slicer on. 
   */
  BITVECTOR_SLICER_ON, 

  /**
   * Slicer off. 
   */
  BITVECTOR_SLICER_OFF, 

  /**
   * Auto enable slicer if problem has only equalities.
   */
  BITVECTOR_SLICER_AUTO

};/* enum BvSlicerMode */

/** Enumeration of sat solvers that can be used. */
enum SatSolverMode {
  SAT_SOLVER_MINISAT,
  SAT_SOLVER_CRYPTOMINISAT,
};/* enum SatSolver */


}/* CVC4::theory::bv namespace */
}/* CVC4::theory namespace */

std::ostream& operator<<(std::ostream& out, theory::bv::BitblastMode mode);
std::ostream& operator<<(std::ostream& out, theory::bv::BvSlicerMode mode);
std::ostream& operator<<(std::ostream& out, theory::bv::SatSolverMode mode);

}/* CVC4 namespace */

#endif /* __CVC4__THEORY__BV__BITBLAST_MODE_H */
