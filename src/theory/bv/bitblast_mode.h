/*********************                                                        */
/*! \file bitblast_mode.h
 ** \verbatim
 ** Original author: Liana Hadarean
 ** Major contributors: none
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2014  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief Bitblasting modes for bit-vector solver.
 **
 ** Bitblasting modes for bit-vector solver.
 **/

#include "cvc4_private.h"

#ifndef __CVC4__THEORY__BV__BITBLAST_MODE_H
#define __CVC4__THEORY__BV__BITBLAST_MODE_H

#include <iostream>

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


}/* CVC4::theory::bv namespace */
}/* CVC4::theory namespace */

std::ostream& operator<<(std::ostream& out, theory::bv::BitblastMode mode) CVC4_PUBLIC;
std::ostream& operator<<(std::ostream& out, theory::bv::BvSlicerMode mode) CVC4_PUBLIC;

}/* CVC4 namespace */

#endif /* __CVC4__THEORY__BV__BITBLAST_MODE_H */
