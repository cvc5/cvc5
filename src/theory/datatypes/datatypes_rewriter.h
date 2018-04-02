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
 /** make tester split
  *
  * Returns the formula (OR is-C1( n ) ... is-Ck( n ) ), where C1...Ck
  * are the constructors of n's type (dt).
  */
 static Node mkSplit(Node n, const Datatype& dt);
 /** returns true iff n is a constructor term with no datatype children */
 static bool isNullaryApplyConstructor(Node n);
 /** returns true iff c is a constructor with no datatype children */
 static bool isNullaryConstructor(const DatatypeConstructor& c);
 /** normalize codatatype constant
  *
  * This returns the normal form of the codatatype constant n. This runs a
  * DFA minimization algorithm based on the private functions below.
  *
  * In particular, we first call collectRefs to setup initial information
  * about what terms occur in n. Then, we run a DFA minimization algorithm to
  * partition these subterms in equivalence classes. Finally, we call
  * normalizeCodatatypeConstantEqc to construct the normalized codatatype
  * constant that is equivalent to n.
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

 /** collect references
  *
  * This function, given as input a codatatype term n, collects the necessary
  * information for constructing a (canonical) codatatype constant that is
  * equivalent to n if one exists, or null otherwise.
  *
  * In particular it returns a term ret such that all non-codatatype datatype
  * subterms of n are replaced by a constant that is equal to them via a
  * (mutually) recursive call to normalizeConstant above. Additionally, this
  * function replaces references to mu-binders with fresh variables.
  * In detail, mu-terms are represented by uninterpreted constants of datatype
  * type that carry their Debruijn index.
  *
  * Consider the example of a codatatype representing a stream of integers:
  *   Stream := cons( head : Int, tail : Stream )
  * The stream 1,0,1,0,1,0... when written in mu-notation is the term:
  *   mu x. cons( 1, mu y. cons( 0, x ) )
  * This is represented in CVC4 by the Node:
  *   cons( 1, cons( 0, c[1] ) )
  * where c[1] is a uninterpreted constant datatype with Debruijn index 1,
  * indicating that c[1] is nested underneath 1 level on the path to the
  * term which it binds. On the other hand, the stream 1,0,0,0,0,... is
  * represented by the codatatype term:
  *   cons( 1, cons( 0, c[0] ) )
  *
  * Subterms that are references to mu-binders in n are replaced by a new
  * variable. If n contains any subterm that is a reference to a mu-binder not
  * bound in n, then we return null. For example we return null when n is:
  *   cons( 1, cons( 0, c[2] ) )
  * since c[2] is not bound by this codatatype term.
  *
  * All valid references to mu-binders are replaced by a variable that is unique
  * for the term it references. For example, for the infinite tree codatatype:
  *   Tree : node( data : Int, left : Tree, right : Tree )
  * If n is the term:
  *   node( 0, c[0], node( 1, c[0], c[1] ) )
  * then the return value ret of this function is:
  *   node( 0, x, node( 1, y, x ) )
  * where x refers to the root of the term and y refers to the right tree of the
  * root.
  *
  * The argument sk stores the current set of node that we are traversing
  * beneath. The argument rf_pending stores, for each node that we are
  * traversing beneath either null or the free variable that we are using to
  * refer to its mu-binder. The remaining arguments store information that is
  * relevant when performing normalization of n using the value of ret:
  *
  * rf : maps subterms of n to the corresponding term in ret for all subterms
  * where the corresponding term in ret is different.
  * terms : stores all subterms of ret.
  * cdts : for each term t in terms, stores whether t is a codatatype.
  */
 static Node collectRef(Node n,
                        std::vector<Node>& sk,
                        std::map<Node, Node>& rf,
                        std::vector<Node>& rf_pending,
                        std::vector<Node>& terms,
                        std::map<Node, bool>& cdts);
 /** normalize codatatype constant eqc
  *
  * This recursive function returns a codatatype constant that is equivalent to
  * n based on a pre-computed partition of the subterms of n into equivalence
  * classes, as stored in the mapping eqc, which maps the subterms of n to
  * equivalence class ids. The arguments eqc_stack and depth store information
  * about the traversal in a term we have recursed, where
  *
  * eqc_stack : maps the depth of each term we have traversed to its equivalence
  * class id.
  * depth : the number of levels which we have traversed.
  */
 static Node normalizeCodatatypeConstantEqc(Node n,
                                            std::map<int, int>& eqc_stack,
                                            std::map<Node, int>& eqc,
                                            int depth);
 /** replace debruijn
  *
  * This function, given codatatype term n, returns a node
  * where all subterms of n that have Debruijn indices that refer to a
  * term of input depth are replaced by orig. For example, for the infinite Tree
  * datatype,
  *   replaceDebruijn( node( 0, c[0], node( 1, c[0], c[1] ) ), t, Tree, 0 )
  * returns
  *   node( 0, t, node( 1, c[0], t ) ).
  */
 static Node replaceDebruijn(Node n,
                             Node orig,
                             TypeNode orig_tn,
                             unsigned depth);
};/* class DatatypesRewriter */

}/* CVC4::theory::datatypes namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */

#endif /* __CVC4__THEORY__DATATYPES__DATATYPES_REWRITER_H */
