/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Morgan Deters
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2025 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Util functions for theory datatypes.
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__DATATYPES__THEORY_DATATYPES_UTILS_H
#define CVC5__THEORY__DATATYPES__THEORY_DATATYPES_UTILS_H

#include <vector>

#include "expr/dtype.h"
#include "expr/node.h"

namespace cvc5::internal {
namespace theory {
namespace datatypes {
namespace utils {

/**
 * Get the index^th selector of datatype constructor dc whose type is dtt. If
 * shareSel is true, this returns the shared selector of dc.
 */
Node getSelector(TypeNode dtt,
                 const DTypeConstructor& dc,
                 size_t index,
                 bool shareSel);
/**
 * Apply the indext^th selector of datatype constructor dc to term n. If
 * shareSel is true, we use the shared selector of dc.
 */
Node applySelector(const DTypeConstructor& dc,
                   size_t index,
                   bool shareSel,
                   const Node& n);

/** get instantiate cons
 *
 * This returns the term C( sel^{C,1}( n ), ..., sel^{C,m}( n ) ),
 * where C is the index^{th} constructor of datatype dt.
 */
Node getInstCons(Node n, const DType& dt, size_t index, bool shareSel);
/**
 * Apply constructor, taking into account whether the datatype is parametric.
 *
 * Return the index^th constructor of dt applied to children, where tn is the
 * datatype type for dt, instantiated if dt is parametric.
 */
Node mkApplyCons(TypeNode tn,
                 const DType& dt,
                 size_t index,
                 const std::vector<Node>& children);
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
 * index of a selector or updater in its constructor.  (Zero is always the
 * first index.)
 */
size_t indexOf(Node n);
/**
 * Get the index of constructor corresponding to selector or updater.
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
 *
 * @param n1 The first term.
 * @param n2 The second term.
 * @param rew The set of entailed equalities.
 * @param checkNdtConst If true, we consider constants (of non-datatype type) to
 * be a conflict.
 */
bool checkClash(Node n1,
                Node n2,
                std::vector<Node>& rew,
                bool checkNdtConst = true);
/**
 * Same as above, but tracks the path to the clashing equality.
 * In particular, path contains the child index to follow in n1 and n2 to
 * find a conflicting value, e.g.
 *    C( x, D( y, z, 7 ) ) = C( w, D( 2, 3, 4) )
 * would return path = { 1, 2 }, referencing the conflicting equality 7=4.
 */
bool checkClash(Node n1,
                Node n2,
                std::vector<Node>& rew,
                bool checkNdtConst,
                std::vector<size_t>& path);

}  // namespace utils
}  // namespace datatypes
}  // namespace theory
}  // namespace cvc5::internal

#endif
