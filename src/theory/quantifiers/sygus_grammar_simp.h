/*********************                                                        */
/*! \file sygus_grammar_proc.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Haniel Barbosa
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2017 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief class for simplifying SyGuS grammars after they are encoded into
 ** datatypes.
 **/

#include "cvc4_private.h"

#ifndef __CVC4__THEORY__QUANTIFIERS__SYGUS_GRAMMAR_SIMP_H
#define __CVC4__THEORY__QUANTIFIERS__SYGUS_GRAMMAR_SIMP_H

#include "theory/quantifiers_engine.h"

namespace CVC4 {
namespace theory {
namespace quantifiers {

class CegConjecture;

/** utility for simplifying grammar and the respective datatypes to avoid
 * spurious enumarations
 */
class SygusGrammarSimplifier
{
public:
 SygusGrammarSimplifier(CegConjecture* p);
 ~SygusGrammarSimplifier() {}
  /** helper function for function process
   * Creates a normalized type from a given type
   * For now only normalizes integer types, e.g.:
   * Int -> x | y | Int + Int | Int - Int | 0 | 1 | ite( Bool, Int, Int ) |
   * c1...cn
   *
   * where c1...cn are additional constants (in the case of large constants
   * appearing in the conjecture).
   *
   * becomes
   *
   * Int -> ite( Bool, Int, Int ) | IntN
   * IntN -> IntX | 0 - IntX
   * IntX -> IntXX + IntX | IntY
   * IntXX -> x
   * IntY -> IntYY + IntY | IntC
   * IntYY -> y
   * IntC -> IntCC + IntC | IntV
   * IntCC -> 1
   * IntV -> 0 | c1...cn
   */
  TypeNode normalizeSygusType(TypeNode tn);
private:
  /** parent conjecture
  * This contains global information about the synthesis conjecture.
  */
  CegConjecture* d_parent;
  /** is the syntax restricted? */
  bool d_is_syntax_restricted;
  /** does the syntax allow ITE expressions? */
  bool d_has_ite;
};

} /* namespace CVC4::theory::quantifiers */
} /* namespace CVC4::theory */
} /* namespace CVC4 */

#endif
