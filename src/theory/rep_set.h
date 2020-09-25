/*********************                                                        */
/*! \file rep_set.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Tim King, Morgan Deters
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Representative set class and utilities
 **/

#include "cvc4_private.h"

#ifndef CVC4__THEORY__REP_SET_H
#define CVC4__THEORY__REP_SET_H

#include <map>
#include <vector>

#include "expr/node.h"
#include "expr/type_node.h"

namespace CVC4 {
namespace theory {

class QuantifiersEngine;

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
  unsigned getNumRepresentatives(TypeNode tn) const;
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

//representative domain
typedef std::vector< int > RepDomain;

class RepBoundExt;

/**
 * Representative set iterator enumeration type, which indicates how the
 * bound on a variable was determined.
 */
enum RsiEnumType
{
  // the bound on the variable is invalid
  ENUM_INVALID = 0,
  // the bound on the variable was determined in the default way, i.e. based
  // on an enumeration of terms in the model.
  ENUM_DEFAULT,
  // The bound on the variable was determined in a custom way, i.e. via a
  // quantifiers module like the BoundedIntegers module.
  ENUM_CUSTOM,
};

/** Rep set iterator.
 *
 * This class is used for iterating over (tuples of) terms
 * in the domain(s) of a RepSet.
 *
 * To use it, first it must
 * be initialized with a call to:
 * - setQuantifier or setFunctionDomain
 * which initializes the d_owner field and sets up
 * initial information.
 *
 * Then, we increment over the tuples of terms in the
 * domains of the owner of this iterator using:
 * - increment and incrementAtIndex
 *
 * TODO (#1199): this class needs further documentation.
 */
class RepSetIterator {
public:
 RepSetIterator(const RepSet* rs, RepBoundExt* rext = nullptr);
 ~RepSetIterator() {}
 /** set that this iterator will be iterating over instantiations for a
  * quantifier */
 bool setQuantifier(Node q);
 /** set that this iterator will be iterating over the domain of a function */
 bool setFunctionDomain(Node op);
 /** increment the iterator */
 int increment();
 /** increment the iterator at index
  * This increments the i^th field of the
  * iterator, for examples, see operator next_i
  * in Figure 2 of Reynolds et al. CADE 2013.
  */
 int incrementAtIndex(int i);
 /** is the iterator finished? */
 bool isFinished() const;
 /** get domain size of the i^th field of this iterator */
 unsigned domainSize(unsigned i);
 /** Get the type of terms in the i^th field of this iterator */
 TypeNode getTypeOf(unsigned i) const;
 /**
  * Get the value for the i^th field in the tuple we are currently considering.
  * If valTerm is true, we return a term instead of a value by calling
  * RepSet::getTermForRepresentative on the value.
  */
 Node getCurrentTerm(unsigned i, bool valTerm = false) const;
 /** get the number of terms in the tuple we are considering */
 unsigned getNumTerms() const { return d_index_order.size(); }
 /** get current terms */
 void getCurrentTerms(std::vector<Node>& terms) const;
 /** get index order, returns var # */
 unsigned getIndexOrder(unsigned v) { return d_index_order[v]; }
 /** get variable order, returns index # */
 unsigned getVariableOrder(unsigned i) { return d_var_order[i]; }
 /** is incomplete
  * Returns true if we are iterating over a strict subset of
  * the domain of the quantified formula or function.
  */
 bool isIncomplete() { return d_incomplete; }
 /** debug print methods */
 void debugPrint(const char* c);
 void debugPrintSmall(const char* c);
 // TODO (#1199): these should be private
 /** enumeration type for each field */
 std::vector<RsiEnumType> d_enum_type;
 /** the current tuple we are considering */
 std::vector<int> d_index;

private:
 /** rep set associated with this iterator */
 const RepSet* d_rs;
 /** rep set external bound information for this iterator */
 RepBoundExt* d_rext;
 /** types we are considering */
 std::vector<TypeNode> d_types;
 /** for each argument, the domain we are iterating over */
 std::vector<std::vector<Node> > d_domain_elements;
 /** initialize
  * This is called when the owner of this iterator is set.
  * It initializes the typing information for the types
  * that are involved in this iterator, initializes the
  * domain elements we are iterating over, and variable
  * and index orderings we are considering.
  */
 bool initialize();
 /** owner
  * This is the term that we are iterating for, which may either be:
  * (1) a quantified formula, or
  * (2) a function.
  */
 Node d_owner;
 /** reset index, 1:success, 0:empty, -1:fail */
 int resetIndex(unsigned i, bool initial = false);
 /** set index order (see below) */
 void setIndexOrder(std::vector<unsigned>& indexOrder);
 /** do reset increment the iterator at index=counter */
 int do_reset_increment(int counter, bool initial = false);
 /** ordering for variables we are iterating over
 *  For example, given reps = { a, b } and quantifier
 *    forall( x, y, z ) P( x, y, z )
 *  with d_index_order = { 2, 0, 1 },
 *    then we consider instantiations in this order:
 *      a/x a/y a/z
 *      a/x b/y a/z
 *      b/x a/y a/z
 *      b/x b/y a/z
 *      ...
 */
 std::vector<unsigned> d_index_order;
 /** Map from variables to the index they are considered at
 * For example, if d_index_order = { 2, 0, 1 }
 *    then d_var_order = { 0 -> 1, 1 -> 2, 2 -> 0 }
 */
 std::map<unsigned, unsigned> d_var_order;
 /** incomplete flag */
 bool d_incomplete;
};/* class RepSetIterator */

/** Representative bound external
 *
 * This class manages bound information
 * for an instance of a RepSetIterator.
 * Its main functionalities are to set
 * bounds on the domain of the iterator
 * over quantifiers and function arguments.
 */
class RepBoundExt
{
 public:
  virtual ~RepBoundExt() {}
  /** set bound
   *
   * This method initializes the vector "elements"
   * with list of terms to iterate over for the i^th
   * field of owner, where owner may be :
   * (1) A function, in which case we are iterating
   *     over domain elements of its argument type,
   * (2) A quantified formula, in which case we are
   *     iterating over domain elements of the type
   *     of its i^th bound variable.
   */
  virtual RsiEnumType setBound(Node owner,
                               unsigned i,
                               std::vector<Node>& elements) = 0;
  /** reset index
   *
   * This method initializes iteration for the i^th
   * field of owner, based on the current state of
   * the iterator rsi. It initializes the vector
   * "elements" with all appropriate terms to
   * iterate over in this context.
   * initial is whether this is the first call
   * to this function for this iterator.
   *
   * This method returns false if we were unable
   * to establish (finite) bounds for the current
   * field we are considering, which indicates that
   * the iterator will terminate with a failure.
   */
  virtual bool resetIndex(RepSetIterator* rsi,
                          Node owner,
                          unsigned i,
                          bool initial,
                          std::vector<Node>& elements)
  {
    return true;
  }
  /** initialize representative set for type
   *
   * Returns true if the representative set associated
   * with this bound has been given a complete interpretation
   * for type tn.
   */
  virtual bool initializeRepresentativesForType(TypeNode tn) { return false; }
  /** get variable order
   * If this method returns true, then varOrder is the order
   * in which we want to consider variables for the iterator.
   * If this method returns false, then varOrder is unchanged
   * and the RepSetIterator is free to choose a default
   * variable order.
   */
  virtual bool getVariableOrder(Node owner, std::vector<unsigned>& varOrder)
  {
    return false;
  }
};

}/* CVC4::theory namespace */
}/* CVC4 namespace */

#endif /* CVC4__THEORY__REP_SET_H */
