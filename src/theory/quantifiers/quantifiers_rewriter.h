/*********************                                                        */
/*! \file quantifiers_rewriter.h
 ** \verbatim
 ** Original author: Morgan Deters
 ** Major contributors: Andrew Reynolds
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2013  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
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

// attribute for "contains instantiation constants from"
struct NestedQuantAttributeId {};
typedef expr::Attribute<NestedQuantAttributeId, Node> NestedQuantAttribute;

class QuantifiersRewriter {
public:
  static bool isClause( Node n );
  static bool isLiteral( Node n );
  static bool isCube( Node n );
private:
  static void addNodeToOrBuilder( Node n, NodeBuilder<>& t );
  static Node mkForAll( std::vector< Node >& args, Node body, Node ipl );
  static void computeArgs( std::vector< Node >& args, std::vector< Node >& activeArgs, Node n );
  static bool hasArg( std::vector< Node >& args, Node n );
  static void setNestedQuantifiers( Node n, Node q );
  static void setNestedQuantifiers2( Node n, Node q, std::vector< Node >& processed );
  static Node computeClause( Node n );
private:
  static Node computeElimSymbols( Node body );
  static Node computeMiniscoping( std::vector< Node >& args, Node body, Node ipl, bool isNested = false );
  static Node computeAggressiveMiniscoping( std::vector< Node >& args, Node body, bool isNested = false );
  static Node computeNNF( Node body );
  static Node computeSimpleIteLift( Node body );
  static Node computeVarElimination( Node body, std::vector< Node >& args, Node& ipl );
  static Node computeCNF( Node body, std::vector< Node >& args, NodeBuilder<>& defs, bool forcePred );
  static Node computePrenex( Node body, std::vector< Node >& args, bool pol );
  static Node computeSplit( Node f, Node body, std::vector< Node >& args );
private:
  enum{
    COMPUTE_ELIM_SYMBOLS = 0,
    COMPUTE_MINISCOPING,
    COMPUTE_AGGRESSIVE_MINISCOPING,
    COMPUTE_NNF,
    COMPUTE_SIMPLE_ITE_LIFT,
    COMPUTE_PRENEX,
    COMPUTE_VAR_ELIMINATION,
    //COMPUTE_FLATTEN_ARGS_UF,
    COMPUTE_CNF,
    COMPUTE_SPLIT,
    COMPUTE_LAST
  };
  static Node computeOperation( Node f, int computeOption );
public:
  static RewriteResponse preRewrite(TNode in);
  static RewriteResponse postRewrite(TNode in);
  static inline void init() {}
  static inline void shutdown() {}
private:
  /** options */
  static bool doMiniscopingNoFreeVar();
  static bool doMiniscopingAnd();
  static bool doOperation( Node f, bool isNested, int computeOption );
public:
  //static Node rewriteQuants( Node n, bool isNested = false );
  //static Node rewriteQuant( Node n, bool isNested = false );
};/* class QuantifiersRewriter */

}/* CVC4::theory::quantifiers namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */

#endif /* __CVC4__THEORY__QUANTIFIERS__QUANTIFIERS_REWRITER_H */

