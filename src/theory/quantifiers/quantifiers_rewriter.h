/*********************                                                        */
/*! \file quantifiers_rewriter.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Morgan Deters, Andrew Reynolds, Tim King
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2016 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Rewriter for the theory of inductive quantifiers
 **
 ** Rewriter for the theory of inductive quantifiers.
 **/

#include "cvc4_private.h"

#ifndef __CVC4__THEORY__QUANTIFIERS__QUANTIFIERS_REWRITER_H
#define __CVC4__THEORY__QUANTIFIERS__QUANTIFIERS_REWRITER_H

#include "theory/rewriter.h"
#include "theory/quantifiers_engine.h"

namespace CVC4 {
namespace theory {
namespace quantifiers {

class QAttributes;

class QuantifiersRewriter {
private:
  static int getPurifyIdLit2( Node n, std::map< Node, int >& visited );
public:
  static bool isClause( Node n );
  static bool isLiteral( Node n );
  static bool isCube( Node n );
private:
  static bool addCheckElimChild( std::vector< Node >& children, Node c, Kind k, std::map< Node, bool >& lit_pol, bool& childrenChanged );
  static void addNodeToOrBuilder( Node n, NodeBuilder<>& t );
  static void computeArgs( std::vector< Node >& args, std::map< Node, bool >& activeMap, Node n, std::map< Node, bool >& visited );
  static void computeArgVec( std::vector< Node >& args, std::vector< Node >& activeArgs, Node n );
  static void computeArgVec2( std::vector< Node >& args, std::vector< Node >& activeArgs, Node n, Node ipl );
  static Node computeProcessTerms2( Node body, bool hasPol, bool pol, std::map< Node, bool >& currCond, int nCurrCond,
                                    std::map< Node, Node >& cache, std::map< Node, Node >& icache,
                                    std::vector< Node >& new_vars, std::vector< Node >& new_conds );
  static void computeDtTesterIteSplit( Node n, std::map< Node, Node >& pcons, std::map< Node, std::map< int, Node > >& ncons, std::vector< Node >& conj );
  static bool isConditionalVariableElim( Node n, int pol=0 );
  static bool isVariableElim( Node v, Node s );
  static void isVariableBoundElig( Node n, std::map< Node, int >& exclude, std::map< Node, std::map< int, bool > >& visited, bool hasPol, bool pol, 
                                   std::map< Node, bool >& elig_vars );
  static bool computeVariableElimLit( Node n, bool pol, std::vector< Node >& args, std::vector< Node >& var, std::vector< Node >& subs,
                                      std::map< Node, std::map< bool, std::map< Node, bool > > >& num_bounds );
  static Node computeVarElimination2( Node body, std::vector< Node >& args, QAttributes& qa );
public:
  static Node computeElimSymbols( Node body );
  static Node computeMiniscoping( std::vector< Node >& args, Node body, QAttributes& qa );
  static Node computeAggressiveMiniscoping( std::vector< Node >& args, Node body );
  //cache is dependent upon currCond, icache is not, new_conds are negated conditions
  static Node computeProcessTerms( Node body, std::vector< Node >& new_vars, std::vector< Node >& new_conds, Node q, QAttributes& qa );
  static Node computeCondSplit( Node body, QAttributes& qa );
  static Node computePrenex( Node body, std::vector< Node >& args, std::vector< Node >& nargs, bool pol, bool prenexAgg );
  static Node computePrenexAgg( Node n, bool topLevel );
  static Node computeSplit( std::vector< Node >& args, Node body, QAttributes& qa );
  static Node computeVarElimination( Node body, std::vector< Node >& args, QAttributes& qa );
private:
  enum{
    COMPUTE_ELIM_SYMBOLS = 0,
    COMPUTE_MINISCOPING,
    COMPUTE_AGGRESSIVE_MINISCOPING,
    COMPUTE_PROCESS_TERMS,
    COMPUTE_PRENEX,
    COMPUTE_VAR_ELIMINATION,
    COMPUTE_COND_SPLIT,
    //COMPUTE_FLATTEN_ARGS_UF,
    //COMPUTE_CNF,
    COMPUTE_LAST
  };
  static Node computeOperation( Node f, int computeOption, QAttributes& qa );
public:
  static RewriteResponse preRewrite(TNode in);
  static RewriteResponse postRewrite(TNode in);
  static inline void init() {}
  static inline void shutdown() {}
private:
  /** options */
  static bool doOperation( Node f, int computeOption, QAttributes& qa );
private:
  static Node preSkolemizeQuantifiers(Node n, bool polarity, std::vector< TypeNode >& fvTypes, std::vector<TNode>& fvs);
public:
  static Node rewriteRewriteRule( Node r );
  static bool containsQuantifiers( Node n );
  static bool isPrenexNormalForm( Node n );
  static Node preprocess( Node n, bool isInst = false );
  static Node mkForAll( std::vector< Node >& args, Node body, QAttributes& qa );
  static Node mkForall( std::vector< Node >& args, Node body, bool marked = false );
};/* class QuantifiersRewriter */

}/* CVC4::theory::quantifiers namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */

#endif /* __CVC4__THEORY__QUANTIFIERS__QUANTIFIERS_REWRITER_H */


