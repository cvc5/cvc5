/*********************                                                        */
/*! \file ho_trigger.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2017 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief higher-order trigger class
 **/

#include "cvc4_private.h"

#ifndef __CVC4__THEORY__QUANTIFIERS__HO_TRIGGER_H
#define __CVC4__THEORY__QUANTIFIERS__HO_TRIGGER_H

#include <map>

#include "expr/node.h"
#include "theory/quantifiers/inst_match.h"
#include "options/quantifiers_options.h"
#include "theory/quantifiers/trigger.h"

namespace CVC4 {
namespace theory {

class QuantifiersEngine;

namespace inst {

class Trigger;

class HigherOrderTrigger : public Trigger {
  friend class Trigger;
protected: 
  /** the applications */
  std::map< Node, std::vector< Node > > d_ho_var_apps;
  /** list of ho variables */
  std::vector< Node > d_ho_var_list;
  /** bound variables, bound variable list for each ho variable */
  std::map< TNode, std::vector< Node > > d_ho_var_bvs;
  std::map< TNode, Node > d_ho_var_bvl;
  /** the set of types of ho variables */
  std::vector< TypeNode > d_ho_var_types;
  /** add higher-order type predicate lemmas */
  int addHoTypeMatchPredicateLemmas();
  /** add an instantiation */
  virtual bool sendInstantiation( InstMatch& m );
private:
  /** current information about match */
  std::map< unsigned, std::vector< Node > > d_lchildren;
  std::map< unsigned, std::map< unsigned, unsigned > > d_arg_to_arg_rep;
  std::map< unsigned, std::map< unsigned, std::vector< Node > > > d_arg_vector;
private:
  /** higher-order pattern unification algorithm */
  bool sendInstantiation( InstMatch& m, unsigned var_index );
  bool sendInstantiationArg( InstMatch& m, unsigned var_index, unsigned vnum, unsigned arg_index,
                             Node lbvl, bool arg_changed );
private:
  HigherOrderTrigger( QuantifiersEngine* qe, Node q, std::vector< Node >& nodes, 
                      std::map< Node, std::vector< Node > >& ho_apps );
  virtual ~HigherOrderTrigger();
public:
  /** collect all top-level HO_APPLY terms whose head is a variable */
  static void collectHoVarApplyTerms( Node q, TNode n, std::map< Node, std::vector< Node > >& apps, 
                                      std::map< TNode, bool >& visited, bool withinApply = false );
  /** collect all top-level HO_APPLY terms whose head is a variable */
  static void collectHoVarApplyTerms( Node q, TNode n, std::map< Node, std::vector< Node > >& apps );
  /** add all available instantiations exhaustively */
  virtual int addInstantiations( InstMatch& baseMatch );
};

}/* CVC4::theory::inst namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */

#endif /* __CVC4__THEORY__QUANTIFIERS__HO_TRIGGER_H */
