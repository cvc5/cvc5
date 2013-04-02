/*********************                                                        */
/*! \file bitblast_strategies.h
 ** \verbatim
 ** Original author: Liana Hadarean
 ** Major contributors: none
 ** Minor contributors (to current version): Dejan Jovanovic, Morgan Deters
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2013  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief Implementation of bitblasting functions for various operators. 
 **
 ** Implementation of bitblasting functions for various operators. 
 **/

#include "cvc4_private.h"

#ifndef __CVC4__BITBLAST__STRATEGIES_H
#define __CVC4__BITBLAST__STRATEGIES_H


#include "expr/node.h"
#include "prop/sat_solver.h"

namespace CVC4 {


namespace theory {
namespace bv {

class Bitblaster;


typedef std::vector<Node>    Bits; 


/** 
 * Default Atom Bitblasting strategies: 
 * 
 * @param node the atom to be bitblasted
 * @param bb the bitblaster
 */

Node UndefinedAtomBBStrategy (TNode node, Bitblaster* bb);                               
Node DefaultEqBB(TNode node, Bitblaster* bb);

Node DefaultUltBB(TNode node, Bitblaster* bb);
Node DefaultUleBB(TNode node, Bitblaster* bb);
Node DefaultUgtBB(TNode node, Bitblaster* bb);
Node DefaultUgeBB(TNode node, Bitblaster* bb);

Node DefaultSltBB(TNode node, Bitblaster* bb);
Node DefaultSleBB(TNode node, Bitblaster* bb);
Node DefaultSgtBB(TNode node, Bitblaster* bb);
Node DefaultSgeBB(TNode node, Bitblaster* bb);

/// other modes
Node AdderUltBB(TNode node, Bitblaster* bb);
Node SltBB(TNode node, Bitblaster* bb);
Node SleBB(TNode node, Bitblaster* bb); 


/** 
 * Default Term Bitblasting strategies
 * 
 * @param node the term to be bitblasted
 * @param bits [output parameter] bits representing the new term 
 * @param bb the bitblaster in which the clauses are added
 */

void UndefinedTermBBStrategy(TNode node, Bits& bits, Bitblaster* bb); 

void DefaultVarBB         (TNode node, Bits& bits, Bitblaster* bb);
void DefaultConstBB       (TNode node, Bits& bits, Bitblaster* bb);
void DefaultNotBB         (TNode node, Bits& bits, Bitblaster* bb);
void DefaultConcatBB      (TNode node, Bits& bits, Bitblaster* bb);
void DefaultAndBB         (TNode node, Bits& bits, Bitblaster* bb);
void DefaultOrBB          (TNode node, Bits& bits, Bitblaster* bb);
void DefaultXorBB         (TNode node, Bits& bits, Bitblaster* bb);
void DefaultXnorBB         (TNode node, Bits& bits, Bitblaster* bb);
void DefaultNandBB        (TNode node, Bits& bits, Bitblaster* bb);
void DefaultNorBB         (TNode node, Bits& bits, Bitblaster* bb);
void DefaultCompBB        (TNode node, Bits& bits, Bitblaster* bb);
void DefaultMultBB        (TNode node, Bits& bits, Bitblaster* bb);
void DefaultPlusBB        (TNode node, Bits& bits, Bitblaster* bb);
void DefaultSubBB         (TNode node, Bits& bits, Bitblaster* bb);
void DefaultNegBB         (TNode node, Bits& bits, Bitblaster* bb);
void DefaultUdivBB        (TNode node, Bits& bits, Bitblaster* bb);
void DefaultUremBB        (TNode node, Bits& bits, Bitblaster* bb);
void DefaultSdivBB        (TNode node, Bits& bits, Bitblaster* bb);
void DefaultSremBB        (TNode node, Bits& bits, Bitblaster* bb);
void DefaultSmodBB        (TNode node, Bits& bits, Bitblaster* bb);
void DefaultShlBB         (TNode node, Bits& bits, Bitblaster* bb);
void DefaultLshrBB        (TNode node, Bits& bits, Bitblaster* bb);
void DefaultAshrBB        (TNode node, Bits& bits, Bitblaster* bb);
void DefaultExtractBB     (TNode node, Bits& bits, Bitblaster* bb);
void DefaultRepeatBB      (TNode node, Bits& bits, Bitblaster* bb);
void DefaultZeroExtendBB  (TNode node, Bits& bits, Bitblaster* bb);
void DefaultSignExtendBB  (TNode node, Bits& bits, Bitblaster* bb);
void DefaultRotateRightBB (TNode node, Bits& bits, Bitblaster* bb);
void DefaultRotateLeftBB  (TNode node, Bits& bits, Bitblaster* bb);


}
}
}

#endif
