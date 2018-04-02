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
#include <unordered_set>

#include "expr/node.h"
#include "options/quantifiers_options.h"
#include "theory/quantifiers/inst_match.h"
#include "theory/quantifiers/ematching/trigger.h"

namespace CVC4 {
namespace theory {
namespace inst {

class Trigger;

/** HigherOrder trigger
 *
 * This extends the trigger class with techniques that post-process
 * instantiations, specified by InstMatch objects, according to a variant of
 * Huet's algorithm. For details, see Chapter 16 of the Handbook of Automated
 * Reasoning (vol. 2), by Gilles Dowek.
 *
 * The main difference between HigherOrderTrigger and Trigger is the function
 * sendInstantiation(...). Recall that this function is called when its
 * underlying IMGenerator generates an InstMatch m using E-matching technique.
 * We enumerate additional instantiations based on m, when the domain of m
 * contains variables of function type.
 *
 * Examples below (f, x, y are universal variables):
 *
 * (EX1): (f x y) matches (k 0 1) in standard E-matching with:
 *
 * f -> k, x -> 0, y -> 1
 *
 * This match is extended to four possible solutions by this class:
 *
 * f -> \ xy. (k x y), x -> 0, y -> 1
 * f -> \ xy. (k 0 y), x -> 0, y -> 1
 * f -> \ xy. (k x 1), x -> 0, y -> 1
 * f -> \ xy. (k 0 1), x -> 0, y -> 1
 *
 *
 * (EX2): Similarly, (f x y) matches (k 0 0) with possible solutions:
 *
 * f -> \ xy. (k x x), x -> 0, y -> 0
 * f -> \ xy. (k y x), x -> 0, y -> 0
 * f -> \ xy. (k 0 x), x -> 0, y -> 0
 * f -> \ xy. (k x y), x -> 0, y -> 0
 * f -> \ xy. (k y y), x -> 0, y -> 0
 * f -> \ xy. (k 0 y), x -> 0, y -> 0
 * f -> \ xy. (k x 0), x -> 0, y -> 0
 * f -> \ xy. (k y 0), x -> 0, y -> 0
 * f -> \ xy. (k 0 0), x -> 0, y -> 0
 *
 *
 * (EX3): (f x y), (f x z) simultaneously match (k 0 1), (k 0 2) with possible
 * solutions:
 *
 * f -> \ xy. (k x y), x -> 0, y -> 1, z -> 2
 * f -> \ xy. (k 0 y), x -> 0, y -> 1, z -> 2
 *
 *
 * This class enumerates the lists above until one instantiation of that form is
 * successfully added via a call to Instantiate::addInstantiation(...)
 *
 *
 * It also implements a way of forcing APPLY_UF to expand to curried HO_APPLY to
 * handle a corner case where there are no matchable ground terms
 * (addHoTypeMatchPredicateLemmas).
 *
 */
class HigherOrderTrigger : public Trigger
{
  friend class Trigger;

 private:
  HigherOrderTrigger(QuantifiersEngine* qe,
                     Node q,
                     std::vector<Node>& nodes,
                     std::map<Node, std::vector<Node> >& ho_apps);
  virtual ~HigherOrderTrigger();

 public:
  /** Collect higher order var apply terms
   *
   * Collect all top-level HO_APPLY terms in n whose head is a variable x in
   * quantified formula q. Append all such terms in apps[x].
   * This method may modify n so that it is in the expected form required for
   * higher-order matching, in particular, APPLY_UF terms with variable
   * operators are converted to curried applications of HO_APPLY.
   */
  static void collectHoVarApplyTerms(Node q,
                                     Node& n,
                                     std::map<Node, std::vector<Node> >& apps);
  /** Collect higher order var apply terms
   *
   * Same as above, but with multiple terms ns.
   */
  static void collectHoVarApplyTerms(Node q,
                                     std::vector<Node>& ns,
                                     std::map<Node, std::vector<Node> >& apps);
  /** add all available instantiations, based on the current context
   *
   * Extends Trigger::addInstantiations to also send
   * lemmas based on addHoTypeMatchPredicateLemmas.
   */
  int addInstantiations() override;

 protected:
  /**
   * Map from function-typed variables to their applications in the quantified
   * formula d_f (member of Trigger).
   */
  std::map<Node, std::vector<Node> > d_ho_var_apps;
  /**
   * List of all function-typed variables that occur as the head of function
   * applications in d_f.
   */
  std::vector<Node> d_ho_var_list;
  /**
   * Cached bound variables and bound variable list for each variable of
   * function type. These are used for constructing lambda terms in
   * instantiations.
   */
  std::map<TNode, std::vector<Node> > d_ho_var_bvs;
  std::map<TNode, Node> d_ho_var_bvl;
  /** the set of types of ho variables */
  std::unordered_set<TypeNode, TypeNodeHashFunction> d_ho_var_types;
  /** add higher-order type predicate lemmas
   *
   * Adds lemmas of the form P( f ), where P is the predicate
   * returned by TermUtil::getHoTypeMatchPredicate( f.getType() ).
   * These lemmas force certain functions f of type tn to appear as
   * first-class terms in the quantifier-free UF solver, where recall a
   * first-class term is one that occurs as an (external) term in its equality
   * engine. These functions f are all operators that have at least one
   * term f(t1...tn) indexed by TermDabatase and are such that
   * f's type is the same as a function-typed variable we
   * are considering in this class (in d_ho_var_apps).
   *
   * TODO: we may eliminate this based on how github issue #1115 is resolved.
   */
  int addHoTypeMatchPredicateLemmas();
  /** send instantiation
   *
  * Sends an instantiation that is equivalent to m via
  * Instantiate::addInstantiation(...). This method may modify m based on
  * imitations and projections (Huet's algorithm), if m was generated by
  * matching ground terms to function applications with variable heads.
  * See examples (EX1)-(EX3) above.
  */
  bool sendInstantiation(InstMatch& m) override;

 private:
  //-------------------- current information about the match
  /**
   * Map from variable position to the arguments of the lambda we generated
   * for that variable.
   *
   * For example (EX4), take a quantified formula:
   *   forall x f1 y f2. (...)
   * Say we generated the match:
   *   x -> 0
   *   f1 -> k1
   *   y -> 1
   *   f2 -> k2
   *   z -> 0
   * where we matched
   *   (f1 x y) with (k1 0 1) and
   *   (f2 x z)  with (k2 0 0)
   * Then the algorithm implemented by this class may modify the match to:
   *   x -> 0
   *   f1 -> (\ x1 x2. (k1 x1 1))
   *   y -> 1
   *   f2 -> (\ x1 x2. (k2 0 x1))
   *   z -> 0
   *
   * In the above (modified) match, the contents of d_lchildren are:
   *   1 -> { k1, x1, 1 }
   *   3 -> { k2, 0, x1 }
   */
  std::map<unsigned, std::vector<Node> > d_lchildren;
  /** map from variable position to the representative variable position.
  * Used when two argument positions of a match are mapped to equal terms.
  *
  * In the above example (EX4), the first and second arguments of
  * the match for f2 are equal.  Thus, in the above example,
  * we have that d_arg_to_arg_rep is:
  *   1 -> { 0 -> 0, 1 -> 1 }
  *   3 -> { 0 -> 0, 1 -> 0 }
  * In other words, the first argument
  */
  std::map<unsigned, std::map<unsigned, unsigned> > d_arg_to_arg_rep;
  /** map from representative argument positions to the equivalence class
   * of argument positions. In the above example (EX4), d_arg_vector is:
   *   1 -> { 0 -> { 0 }, 1 -> { 1 } }
   *   3 -> { 0 -> { 0, 1 } }
   */
  std::map<unsigned, std::map<unsigned, std::vector<Node> > > d_arg_vector;
  //-------------------- end current information about the match

  /** higher-order pattern unification algorithm
   *
  * Sends an instantiation that is equivalent to m via
  * d_quantEngine->addInstantiation(...),
  * based on Huet's algorithm.
  *
  * This is a helper function of sendInstantiation( m ) above.
  *
  * var_index is the index of the variable in m that we are currently processing
  *   i.e. we are processing the var_index^{th} higher-order variable.
  *
  * For example, say we are processing the match from (EX4) above.
  *   when var_index = 0,1, we are processing possibilities for
  *    instantiation of f1,f2 respectively.
  */
  bool sendInstantiation(InstMatch& m, unsigned var_index);
  /** higher-order pattern unification algorithm
   * Sends an instantiation that is equivalent to m via
   * d_quantEngine->addInstantiation(...).
   * This is a helper function of sendInstantiation( m, var_index ) above.
   *
   * var_index is the index of the variable in m that we are currently
   * processing
   *   i.e. we are processing the var_index^{th} higher-order variable.
   * vnum maps var_index to the actual variable number in m
   * arg_index is the argument of the lambda term we are currently considering
   * lbvl is the bound variable list associated with the term in m we are
   * currently modifying
   * arg_changed is whether we have modified m.
   *
   * For example, say we have modified our match from (EX4) to:
   *   x -> 0
   *   f1 -> (\ x1 x2. (k1 x1 1))
   *   y -> 1
   *   f2 -> (\ x1 x2. (k2 0 ?))
   *   z -> 0
   * That is, we are currently considering possibilities for the second
   * argument of the body for f2.
   * Then:
   *   var_index = 1,
   *   vnum = 3 (f2 is the 3^rd variable of our quantified formula)
   *   arg_index = 1,
   *   lbvl is d_ho_var_bvl[f2], and
   *   arg_changed is true, since we modified at least one previous
   *     argument of f1 or f2.
   */
  bool sendInstantiationArg(InstMatch& m,
                            unsigned var_index,
                            unsigned vnum,
                            unsigned arg_index,
                            Node lbvl,
                            bool arg_changed);
};

} /* CVC4::theory::inst namespace */
} /* CVC4::theory namespace */
} /* CVC4 namespace */

#endif /* __CVC4__THEORY__QUANTIFIERS__HO_TRIGGER_H */
