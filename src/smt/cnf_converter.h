/*********************                                           -*- C++ -*-  */
/** cnf_converter.h
 ** Original author: mdeters
 ** Major contributors: dejan
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009 The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.
 **
 ** A CNF converter for CVC4.
 **/

#ifndef __CVC4__SMT__CNF_CONVERTER_H
#define __CVC4__SMT__CNF_CONVERTER_H

#include "expr/node_builder.h"
#include "expr/node.h"
#include "smt/cnf_conversion.h"

#include <map>

namespace CVC4 {
namespace smt {

class CnfConverter {

private:

  /** Our node manager */
  NodeManager *d_nm;

  /** The type of conversion this converter performs */
  CVC4::CnfConversion d_conversion;

  /** Map of already-converted Nodes */
  std::map<Node, Node> d_conversionMap;

  /**
   * Returns true iff the CNF conversion for the Node was cached
   * previously.
   */
  bool conversionMapped(const Node& n) {
    return d_conversionMap.find(n) != d_conversionMap.end();
  }

  /**
   * Returns true iff the CNF conversion for the Node was cached
   * previously.
   */
  Node getConversionMap(const Node& n) {
    return d_conversionMap[n];
  }

  /**
   * Cache a new CNF conversion.
   */
  void mapConversion(const Node& n, const Node& m) {
    d_conversionMap[n] = m;
  }

  /**
   * Compress a NOT: do NNF transformation plus a bit.  Does DNE,
   * NOT FALSE ==> TRUE, NOT TRUE ==> FALSE, and pushes NOT inside
   * of ANDs and ORs.  Calls doConvert() on subnodes.
   */
  Node compressNOT(const Node& e, NodeBuilder<>* sideConditions);

  /**
   * Flatten a Node of kind K.  K here is going to be AND or OR.
   * "Flattening" means to take all children of the Node with the same
   * kind and hoist their children to the top-level.  So e.g.
   * (AND (AND x y) (AND (AND z)) w)  ==>  (AND x y z w).
   */
  template <CVC4::Kind K>
  Node flatten(const Node& e, NodeBuilder<>* sideConditions);

  /**
   * Do a direct CNF conversion (with possible exponential blow-up in
   * the number of clauses).  No new variables are introduced.  The
   * output is equivalent to the input.
   */
  Node directConvert(const Node& e, NodeBuilder<>* sideConditions);

  /**
   * Helper method for "direct" CNF preprocessing.  CNF-converts an OR.
   */
  void directOrHelper(Node::iterator p,
                      Node::iterator end,
                      NodeBuilder<>& result,
                      NodeBuilder<>* sideConditions);

  /**
   * Do a satisfiability-preserving CNF conversion with variable
   * introduction.  Doesn't suffer from exponential blow-up in the
   * number of clauses, but new variables are introduced and the
   * output is equisatisfiable (but not equivalent) to the input.
   */
  Node varIntroductionConvert(const Node& e, NodeBuilder<>* sideConditions);

  /**
   * Convert an expression into CNF.  If a conversion already exists
   * for the Node, it is returned.  If a conversion doesn't exist, it
   * is computed and returned (caching the result).
   */
  Node doConvert(const Node& e, NodeBuilder<>* sideconditions);

public:

  /**
   * Construct a CnfConverter.
   */
  CnfConverter(NodeManager* nm, CVC4::CnfConversion cnv = CNF_VAR_INTRODUCTION) :
    d_nm(nm),
    d_conversion(cnv) {}

  /**
   * Convert an expression into CNF.  If a conversion already exists
   * for the Node, it is returned.  If a conversion doesn't exist, it
   * is computed and returned (caching the result).
   */
  Node convert(const Node& e);

};/* class CnfConverter */

template <CVC4::Kind K>
struct flatten_traits;

template <>
struct flatten_traits<AND> {
  static const CVC4::Kind ignore   = TRUE;  // TRUE  AND x == x
  static const CVC4::Kind shortout = FALSE; // FALSE AND x == FALSE
};

template <>
struct flatten_traits<OR> {
  static const CVC4::Kind ignore   = FALSE; // FALSE OR x == x
  static const CVC4::Kind shortout = TRUE;  // TRUE  OR x == TRUE
};

template <CVC4::Kind K>
Node CnfConverter::flatten(const Node& e, NodeBuilder<>* sideConditions) {
  Assert(e.getKind() == K);

  NodeBuilder<> n(K);

  for(Node::iterator i = e.begin(); i != e.end(); ++i) {
    Node f = doConvert(*i, sideConditions);
    if(f.getKind() == K) {
      for(Node::iterator j = f.begin(); j != f.end(); ++j) {
        n << *j;
      }
    } else if(f.getKind() == flatten_traits<K>::ignore) {
      /* do nothing */
    } else if(f.getKind() == flatten_traits<K>::shortout) {
      return f;
    } else {
      n << f;
    }
  }

  return n;
}

}/* CVC4::smt namespace */
}/* CVC4 namespace */

#endif /* __CVC4__SMT__CNF_CONVERTER_H */
