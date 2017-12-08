/*********************                                                        */
/*! \file datatypes_rewriter.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Morgan Deters, Paul Meng
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2017 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Rewriter for the theory of (co)inductive datatypes
 **
 ** Rewriter for the theory of (co)inductive datatypes.
 **/

#include "cvc4_private.h"

#ifndef __CVC4__THEORY__DATATYPES__DATATYPES_REWRITER_H
#define __CVC4__THEORY__DATATYPES__DATATYPES_REWRITER_H

#include "expr/node_manager_attributes.h"
#include "options/datatypes_options.h"
#include "theory/rewriter.h"
#include "theory/type_enumerator.h"

namespace CVC4 {
namespace theory {
namespace datatypes {

class DatatypesRewriter {
public:
 static RewriteResponse postRewrite(TNode in);

 static RewriteResponse preRewrite(TNode in);

 static inline void init() {}
 static inline void shutdown() {}
 /** get instantiate cons
  *
  * This returns the term C( sel^{C,1}( n ), ..., sel^{C,m}( n ) ),
  * where C is the index^{th} constructor of datatype dt.
  */
 static Node getInstCons(Node n, const Datatype& dt, int index);
 /** is instantiation cons
  *
  * If this method returns a value >=0, then that value, call it index,
  * is such that n = C( sel^{C,1}( t ), ..., sel^{C,m}( t ) ),
  * where C is the index^{th} constructor of dt.
  */
 static int isInstCons(Node t, Node n, const Datatype& dt);
 /** is tester
  *
  * This method returns a value >=0 if n is a tester predicate. The return
  * value indicates the constructor index that the tester n is for. If this
  * method returns a value >=0, then it updates a to the argument that the
  * tester n applies to.
  */
 static int isTester(Node n, Node& a);
 /** is tester, same as above but does not update an argument */
 static int isTester(Node n);
 /** make tester is-C( n ), where C is the i^{th} constructor of dt */
 static Node mkTester(Node n, int i, const Datatype& dt);
 /** returns true iff n is a constructor term with no datatype children */
 static bool isNullaryApplyConstructor(Node n);
 /** returns true iff c is a constructor with no datatype children */
 static bool isNullaryConstructor(const DatatypeConstructor& c);
 /** normalize codatatype constant
  *
  * This returns the normal form of the codatatype constant n. This runs a
  * DFA minimization algorithm based on the private functions below.
  */
 static Node normalizeCodatatypeConstant(Node n);
 /** normalize constant
  *
  * This method returns the normal form of n, which calls the above function
  * on all top-level codatatype subterms of n.
  */
 static Node normalizeConstant(Node n);
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
 static bool checkClash(Node n1, Node n2, std::vector<Node>& rew);

private:
 /** rewrite constructor term in */
 static RewriteResponse rewriteConstructor(TNode in);
 /** rewrite selector term in */
 static RewriteResponse rewriteSelector(TNode in);
 /** rewrite tester term in */
 static RewriteResponse rewriteTester(TNode in);

 /** TODO (#1436) document these */
 static Node collectRef(Node n,
                        std::vector<Node>& sk,
                        std::map<Node, Node>& rf,
                        std::vector<Node>& rf_pending,
                        std::vector<Node>& terms,
                        std::map<Node, bool>& cdts);
 // eqc_stack stores depth
 static Node normalizeCodatatypeConstantEqc(Node n,
                                            std::map<int, int>& eqc_stack,
                                            std::map<Node, int>& eqc,
                                            int depth);
 static Node replaceDebruijn(Node n,
                             Node orig,
                             TypeNode orig_tn,
                             unsigned depth);
};/* class DatatypesRewriter */

}/* CVC4::theory::datatypes namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */

#endif /* __CVC4__THEORY__DATATYPES__DATATYPES_REWRITER_H */
