/*********************                                                        */
/*! \file sygus_sampler.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2017 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief sygus_sampler
 **/

#include "cvc4_private.h"

#ifndef __CVC4__THEORY__QUANTIFIERS__SYGUS_SAMPLER_H
#define __CVC4__THEORY__QUANTIFIERS__SYGUS_SAMPLER_H

#include <map>
#include "theory/quantifiers/term_database_sygus.h"

namespace CVC4 {
namespace theory {
namespace quantifiers {

/** abstract evaluator class 
 * 
 * This class is used for the LazyTrie data structure below.
 */
class LazyTrieEvaluator
{
public:
  virtual Node evaluate(Node n, unsigned index) = 0;
};
  
/** LazyTrie
 * 
 * This is a trie where terms are added in a lazy fashion. This data structure
 * is useful, for instance, when we are only interested in when two terms
 * map to the same node in the trie but we need not care about computing
 * exactly where they are.
 * 
 * In other words, when a term n is added to this trie, we do not insist
 * that n is placed at the maximal depth of the trie. Instead, we place n at a 
 * minimal depth node that has no children. In this case we say n is partially
 * evaluated in this trie.
 * 
 * This class relies on an abstract evaluator interface above, which evaluates
 * nodes for indices.
 * 
 * For example, say we have terms a, b, c and an evaluator ev where:
 *   ev->evaluate( a, 0,1,2 ) = 0, 5, 6
 *   ev->evaluate( b, 0,1,2 ) = 1, 3, 0  
 *   ev->evaluate( c, 0,1,2 ) = 1, 3, 2
 * After adding a to the trie, we get:
 *   root: a
 * After adding b to the resulting trie, we get:
 *   root: null
 *     d_children[0]: a
 *     d_children[1]: b
 * After adding c to the resulting trie, we get:
 *   root: null
 *     d_children[0]: a
 *     d_children[1]: null
 *       d_children[3]: null
 *         d_children[0] : b
 *         d_children[2] : c
 * Notice that we need not call ev->evalute( a, 1 ) and ev->evalute( a, 2 ).
 */
class LazyTrie {
 public:
  LazyTrie() {}
  ~LazyTrie() {}
  /** the data at this node, which may be partially evaluated */
  Node d_lazy_child;
  /** the children of this node */
  std::map<Node, LazyTrie> d_children;
  /** clear the trie */
  void clear() { d_children.clear(); }
  /** add n to the trie
   * 
   * This function returns a node that is mapped to the same node in the trie
   * if one exists, or n otherwise.
   * 
   * ev is an evaluator which determines where n is placed in the trie
   * index is the depth of this node
   * ntotal is the maximal depth of the trie
   */
  Node add(Node n, LazyTrieEvaluator* ev,unsigned index, unsigned ntotal);
};  

  
/** SygusSampler
 * 
 */
class SygusSampler : public LazyTrieEvaluator
{
public:
  SygusSampler();
  virtual ~SygusSampler(){}
  /** initialize */
  void initialize( TermDbSygus * tds, Node f, unsigned nsamples );
  /** register */
  Node registerTerm( Node n );
  /** is contiguous 
   * 
   * This returns whether n's free variables are a prefix of the list of 
   * variables in d_type_vars for each type. For instance, if
   * d_type_vars[Int] = { x, y }, then 0, x, x+y, y+x are contiguous but y is 
   * not. This is useful for excluding terms from consideration that are
   * alpha-equivalent to others.
   */
  bool isContiguous( Node n );
  /** is ordered 
   * 
   * This returns whether n's free variables are in order with respect to
   * variables in d_type_vars for each type. For instance, if
   * d_type_vars[Int] = { x, y }, then 0, x, x+y are contiguous but y and y+x 
   * are not.
   */
  bool isOrdered( Node n );
  /** evaluate n on sample point index */
  Node evaluate(Node n, unsigned index);
private:
  /** sygus term database of d_qe */
  TermDbSygus * d_tds;
  /** samples */
  std::vector< std::vector< Node > > d_samples;
  /** type of nodes we will be registering with this class */
  TypeNode d_ftn;
  /** type variables
   *
   * For each type, a list of variables in the grammar we are considering, for 
   * that type. 
   */
  std::map< TypeNode, std::vector< Node > > d_type_vars;
  /**
   * A map all variables in the grammar we are considering to their index in 
   * d_type_vars. 
   */
  std::map< Node, unsigned > d_var_index;
  /** constants 
   * 
   * For each type, a list of constants in the grammar we are considering, for
   * that type.
   */
  std::map< TypeNode, std::vector< Node > > d_type_consts;
  /** the lazy trie */
  LazyTrie d_trie;
  /** is this sampler valid?
   * 
   * A sampler can be invalid if sample points cannot be generated for a type
   * of an argument to function f.
   */
  bool d_is_valid;
  /** get random value for a type */
  Node getRandomValue( TypeNode tn );
};


} /* CVC4::theory::quantifiers namespace */
} /* CVC4::theory namespace */
} /* CVC4 namespace */

#endif /* __CVC4__THEORY__QUANTIFIERS__SYGUS_SAMPLER_H */
