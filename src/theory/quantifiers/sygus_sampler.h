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
#include "theory/quantifiers_engine.h"
#include "theory/quantifiers/term_database_sygus.h"

namespace CVC4 {
namespace theory {
namespace quantifiers {

/** abstract evaluator class */
class LazyTrieEvaluator
{
public:
  virtual Node evaluate(Node n, unsigned index) = 0;
};
  
/** this class is an index of candidate solutions for PBE synthesis */
class LazyTrie {
 public:
  LazyTrie() {}
  ~LazyTrie() {}
  Node d_lazy_child;
  std::map<Node, LazyTrie> d_children;
  void clear() { d_children.clear(); }
  Node add(Node n, LazyTrieEvaluator* ev,unsigned index, unsigned ntotal);
};  

  
/** SygusSampler
 * 
 */
class SygusSampler : public LazyTrieEvaluator
{
public:
  SygusSampler( QuantifiersEngine * qe, Node f, unsigned nsamples );
  virtual ~SygusSampler(){}
  /** register */
  Node registerTerm( Node n );
  /** evaluate n on sample point index */
  Node evaluate(Node n, unsigned index);
private:
  /** reference to quantifier engine */
  QuantifiersEngine * d_qe;
  /** sygus term database of d_qe */
  TermDbSygus * d_tds;
  /** samples */
  std::vector< std::vector< Node > > d_samples;
  /** type of nodes we will be registering with this class */
  TypeNode d_ftn;
  /** for each type, a list of variables for that type */
  std::map< TypeNode, std::vector< Node > > d_type_vars;
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
