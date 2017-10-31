/*********************                                                        */
/*! \file skolemize.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2017 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief utilities for skolemization
 **/

#include "cvc4_private.h"

#ifndef __CVC4__THEORY__QUANTIFIERS__SKOLEMIZE_H
#define __CVC4__THEORY__QUANTIFIERS__SKOLEMIZE_H

#include <unordered_map>
#include <unordered_set>

#include "context/cdhashmap.h"
#include "expr/datatype.h"
#include "expr/node.h"
#include "expr/type_node.h"
#include "theory/quantifiers/quant_util.h"

namespace CVC4 {
namespace theory {
namespace quantifiers {

/** Skolemization utility 
 * 
 * This class constructs Skolemization lemmas.
 * Given a quantified formula q = (forall x. P),
 * its skolemization lemma is of the form:
 *   (~ forall x. P ) => ~P * { x -> d_skolem_constants[q] }
 * 
 * This class also incorporates techniques for
 * skolemization with "inductive strenghtening", see
 * Section 2 of Reynolds et al., "Induction for SMT 
 * Solvers", VMCAI 2015. In the case that x is an inductive
 * datatype or an integer, then we may strengthen the conclusion
 * based on well-founded induction. 
 * 
 * Inductive strenghtening is not enabled by
 * default and can be enabled by option:
 *   --quant-ind
 */
class Skolemize
{
  typedef context::CDHashMap< Node, bool, NodeHashFunction > BoolMap;
 public:
  Skolemize(QuantifiersEngine * qe, context::UserContext* u);
  ~Skolemize(){}
  /** skolemize quantified formula q 
   * If the return value ret of this function
   * is non-null, then ret is a skolemization lemma for q.
   */
  Node process( Node q );
  /** get skolem constants for quantified q
   */
  bool getSkolemConstants( Node q, std::vector< Node >& skolems );
  /** get skolem constant */
  Node getSkolemConstant( Node q, unsigned i );
  /** make the skolemized body f[e/x] */
  static Node mkSkolemizedBody( Node f, Node n, std::vector< TypeNode >& fvTypes, std::vector< TNode >& fvs,
                                std::vector< Node >& sk, Node& sub, std::vector< unsigned >& sub_vars );
  /** get the skolemized body */
  Node getSkolemizedBody( Node f);
  /** is induction variable */
  static bool isInductionTerm( Node n );
  /** print all skolemizations 
   * This is used for the command line option 
   *   --dump-instantiations
   * which prints an informal justification 
   * of steps taken by the quantifiers module.
   * Returns true if we printed at least one
   * skolemization.
   */
  bool printSkolemization( std::ostream& out );
 private:  
  /** get self selectors 
   * For datatype constructor dtc with type dt,
   * this collects the set of datatype selector applications,
   * applied to term n, whose return type in ntn, and stores
   * them in the vector selfSel.
   */
  static void getSelfSel( const Datatype& dt, const DatatypeConstructor& dc, Node n, TypeNode ntn, std::vector< Node >& selfSel );
  /** quantifiers engine that owns this module */
  QuantifiersEngine* d_quantEngine;
  /** quantifiers that have been skolemized */
  BoolMap d_skolemized;
  /** map from universal quantifiers to the list of skolem constants */
  std::unordered_map< Node, std::vector< Node >, NodeHashFunction > d_skolem_constants;
  /** map from universal quantifiers to their skolemized body */
  std::unordered_map< Node, Node, NodeHashFunction > d_skolem_body;
};
  
}/* CVC4::theory::quantifiers namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */

#endif /* __CVC4__THEORY__QUANTIFIERS__SKOLEMIZE_H */
