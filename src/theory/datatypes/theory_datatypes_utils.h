/*********************                                                        */
/*! \file theory_datatypes_utils.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Morgan Deters
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Util functions for theory datatypes.
 **
 ** Util functions for theory datatypes.
 **/

#include "cvc4_private.h"

#ifndef CVC4__THEORY__STRINGS__THEORY_DATATYPES_UTILS_H
#define CVC4__THEORY__STRINGS__THEORY_DATATYPES_UTILS_H

#include <vector>

#include "expr/dtype.h"
#include "expr/node.h"
#include "expr/node_manager_attributes.h"

namespace CVC4 {
namespace theory {
namespace datatypes {
namespace utils {

/** get instantiate cons
 *
 * This returns the term C( sel^{C,1}( n ), ..., sel^{C,m}( n ) ),
 * where C is the index^{th} constructor of datatype dt.
 */
Node getInstCons(Node n, const DType& dt, int index);
/** is instantiation cons
 *
 * If this method returns a value >=0, then that value, call it index,
 * is such that n = C( sel^{C,1}( t ), ..., sel^{C,m}( t ) ),
 * where C is the index^{th} constructor of dt.
 */
int isInstCons(Node t, Node n, const DType& dt);
/** is tester
 *
 * This method returns a value >=0 if n is a tester predicate. The return
 * value indicates the constructor index that the tester n is for. If this
 * method returns a value >=0, then it updates a to the argument that the
 * tester n applies to.
 */
int isTester(Node n, Node& a);
/** is tester, same as above but does not update an argument */
int isTester(Node n);
/**
 * Get the index of a constructor or tester in its datatype, or the
 * index of a selector in its constructor.  (Zero is always the
 * first index.)
 */
size_t indexOf(Node n);
/**
 * Get the index of constructor corresponding to selector.
 * (Zero is always the first index.)
 */
size_t cindexOf(Node n);
/**
 * Get the datatype of n.
 */
const DType& datatypeOf(Node n);
/** make tester is-C( n ), where C is the i^{th} constructor of dt */
Node mkTester(Node n, int i, const DType& dt);
/** make tester split
 *
 * Returns the formula (OR is-C1( n ) ... is-Ck( n ) ), where C1...Ck
 * are the constructors of n's type (dt).
 */
Node mkSplit(Node n, const DType& dt);
/** returns true iff n is a constructor term with no datatype children */
bool isNullaryApplyConstructor(Node n);
/** returns true iff c is a constructor with no datatype children */
bool isNullaryConstructor(const DTypeConstructor& c);
/** check clash
 *
 * This method returns true if and only if n1 and n2 have a skeleton that has
 * conflicting constructors at some term position.
 * Examples of terms that clash are:
 *   C( x, y ) and D( z )
 *   C( D( x ), y ) and C( E( x ), y )
 * Examples of terms that do not clash are:
 *   C( x, y ) and C( D( x ), y )
 *   C( D( x ), y ) and C( x, E( z ) )
 *   C( x, y ) and z
 */
bool checkClash(Node n1, Node n2, std::vector<Node>& rew);

}  // namespace utils
}  // namespace datatypes
}  // namespace theory
}  // namespace CVC4

#endif
