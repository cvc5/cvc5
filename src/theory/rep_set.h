/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Tim King, Aina Niemetz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Representative set class.
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__REP_SET_H
#define CVC5__THEORY__REP_SET_H

#include <map>
#include <vector>

#include "expr/node.h"
#include "expr/type_node.h"

namespace cvc5::internal {
namespace theory {

/** representative set
 *
 * This class contains finite lists of values for types, typically values and
 * types that exist
 * in the equality engine of a model object.  In the following, "representative"
 * means a value that exists in this set.
 *
 * This class is used for finite model finding and other exhaustive
 * instantiation-based
 * methods. The class goes beyond just maintaining a list of values that occur
 * in the equality engine in the following ways:
 
 * (1) It maintains a partial mapping from representatives to a term that has
 * that value in the current
 * model.  This is important because algorithms like the instantiation method in
 * Reynolds et al CADE 2013
 * act on "term models" where domains in models are interpreted as a set of
 * representative terms. Hence,
 * instead of instantiating with e.g. uninterpreted constants u, we instantiate
 * with the corresponding term that is interpreted as u.
 
 * (2) It is mutable, calls to add(...) and complete(...) may modify this class
 * as necessary, for instance
 * in the case that there are no ground terms of a type that occurs in a
 * quantified formula, or for
 * exhaustive instantiation strategies that enumerate over small interpreted
 * finite types.
 */
class RepSet {
 public:
  RepSet(){}

  /** map from types to the list of representatives
   * TODO : as part of #1199, encapsulate this
   */
  std::map< TypeNode, std::vector< Node > > d_type_reps;
  /** clear the set */
  void clear();
  /** does this set have representatives of type tn? */
  bool hasType(TypeNode tn) const { return d_type_reps.count(tn) > 0; }
  /** does this set have representative n of type tn? */
  bool hasRep(TypeNode tn, Node n) const;
  /** get the number of representatives for type */
  size_t getNumRepresentatives(TypeNode tn) const;
  /** get representative at index */
  Node getRepresentative(TypeNode tn, unsigned i) const;
  /**
   * Returns the representatives of a type for a `type_node` if one exists.
   * Otherwise, returns nullptr.
   */
  const std::vector<Node>* getTypeRepsOrNull(TypeNode type_node) const;

  /** add representative n for type tn, where n has type tn */
  void add( TypeNode tn, Node n );
  /** returns index in d_type_reps for node n */
  int getIndexFor( Node n ) const;
  /** complete the list for type t
   * Resets d_type_reps[tn] and repopulates by running the type enumerator for
   * that type exhaustively.
   * This should only be called for small finite interpreted types.
   */
  bool complete( TypeNode t );
  /** get term for representative
   * Returns a term that is interpreted as representative n in the current
   * model, null otherwise.
   */
  Node getTermForRepresentative(Node n) const;
  /** set term for representative
   * Called when t is interpreted as value n. Subsequent class to
   * getTermForRepresentative( n ) will return t.
   */
  void setTermForRepresentative(Node n, Node t);
  /** get existing domain value, with possible exclusions
    *   This function returns a term in d_type_reps[tn] but not in exclude
    */
  Node getDomainValue(TypeNode tn, const std::vector<Node>& exclude) const;
  /** debug print */
  void toStream(std::ostream& out);

 private:
  /** whether the list of representatives for types are complete */
  std::map<TypeNode, bool> d_type_complete;
  /** map from representatives to their index in d_type_reps */
  std::map<Node, int> d_tmap;
  /** map from values to terms they were assigned for */
  std::map<Node, Node> d_values_to_terms;
};/* class RepSet */


}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5__THEORY__REP_SET_H */
