/*********************                                                        */
/*! \file sygus_repair_const.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Haniel Barbosa, Mathias Preiner
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief sygus_repair_const
 **/

#include "cvc4_private.h"

#ifndef CVC4__THEORY__QUANTIFIERS__SYGUS_REPAIR_CONST_H
#define CVC4__THEORY__QUANTIFIERS__SYGUS_REPAIR_CONST_H

#include <unordered_set>
#include "expr/node.h"
#include "theory/logic_info.h"

namespace CVC4 {
namespace theory {

class QuantifiersEngine;

namespace quantifiers {

class CegConjecture;
class TermDbSygus;

/** SygusRepairConst
 *
 * This module is used to repair portions of candidate solutions. In particular,
 * given a synthesis conjecture:
 *   exists f. forall x. P( f, x )
 * and a candidate solution f = \x. t[x,r] where r are repairable terms, this
 * function checks whether there exists a term of the form \x. t[x,c'] for some
 * constants c' such that:
 *   forall x. P( (\x. t[x,c']), x )  [***]
 * is satisfiable, where notice that the above formula after beta-reduction may
 * be one in pure first-order logic in a decidable theory (say linear
 * arithmetic). To check this, we invoke a separate instance of the SmtEngine
 * within repairSolution(...) below, which if satisfiable gives us the
 * valuation for c'.
 */
class SygusRepairConst
{
 public:
  SygusRepairConst(QuantifiersEngine* qe);
  ~SygusRepairConst() {}
  /** initialize
   *
   * Initialize this class with the base instantiation (body) of the sygus
   * conjecture (see SynthConjecture::d_base_inst) and its candidate variables
   * (see SynthConjecture::d_candidates).
   */
  void initialize(Node base_inst, const std::vector<Node>& candidates);
  /** repair solution
   *
   * This function is called when candidates -> candidate_values is a (failed)
   * candidate solution for the synthesis conjecture.
   *
   * If this function returns true, then this class adds to repair_cv the
   * repaired version of the solution candidate_values for each candidate,
   * where for each index i, repair_cv[i] is obtained by replacing constant
   * subterms in candidate_values[i] with others, and
   *    candidates -> repair_cv
   * is a solution for the synthesis conjecture associated with this class.
   * Moreover, it is the case that
   *    repair_cv[j] != candidate_values[j], for at least one j.
   * We always consider applications of the "any constant" constructors in
   * candidate_values to be repairable. In addition, if the flag
   * useConstantsAsHoles is true, we consider all constants whose (sygus) type
   * admit alls constants to be repairable.
   * The repaired solution has the property that it satisfies the synthesis
   * conjecture whose body is given by sygusBody.
   */
  bool repairSolution(Node sygusBody,
                      const std::vector<Node>& candidates,
                      const std::vector<Node>& candidate_values,
                      std::vector<Node>& repair_cv,
                      bool useConstantsAsHoles = false);
  /**
   * Same as above, but where sygusBody is the body (base_inst) provided to the
   * call to initialize of this class.
   */
  bool repairSolution(const std::vector<Node>& candidates,
                      const std::vector<Node>& candidate_values,
                      std::vector<Node>& repair_cv,
                      bool useConstantsAsHoles = false);
  /**
   * Return whether this module has the possibility to repair solutions. This is
   * true if this module has been initialized, and at least one candidate has
   * an "any constant" constructor.
   */
  bool isActive() const;
  /** must repair?
   *
   * This returns true if n must be repaired for it to be a valid solution.
   * This corresponds to whether n contains a subterm that is a symbolic
   * constructor like the "any constant" constructor.
   */
  static bool mustRepair(Node n);

 private:
  /** reference to quantifier engine */
  QuantifiersEngine* d_qe;
  /** pointer to the sygus term database of d_qe */
  TermDbSygus* d_tds;
  /**
   * The "base instantiation" of the deep embedding form of the synthesis
   * conjecture associated with this class, see CegConjecture::d_base_inst.
   */
  Node d_base_inst;
  /**
   * whether any sygus type for the candidate variables of d_base_inst (the
   * syntactic restrictions) allows all constants. If this flag is false, then
   * this class is a no-op.
   */
  bool d_allow_constant_grammar;
  /** map from skeleton variables to first-order variables */
  std::map<Node, Node> d_sk_to_fo;
  /** reverse map of d_sk_to_fo */
  std::map<Node, Node> d_fo_to_sk;
  /** a cache of satisfiability queries of the form [***] above we have tried */
  std::unordered_set<Node, NodeHashFunction> d_queries;
  /**
   * Register information for sygus type tn, tprocessed stores the set of
   * already registered types.
   */
  void registerSygusType(TypeNode tn, std::map<TypeNode, bool>& tprocessed);
  /** is repairable?
   *
   * This returns true if n can be repaired by this class. In particular, we
   * return true if n is an "any constant" constructor, or it is a constructor
   * for a constant in a type that allows all constants and useConstantsAsHoles
   * is true.
   */
  static bool isRepairable(Node n, bool useConstantsAsHoles);
  /** get skeleton
   *
   * Returns a skeleton for sygus datatype value n, where the subterms of n that
   * are repairable are replaced by free variables. Since we are interested in
   * returning canonical skeletons, the free variables we use in this
   * replacement are taken from TermDbSygus, where we track indices
   * in free_var_count. Variables we introduce in this way are added to sk_vars.
   * The mapping sk_vars_to_subs contains entries v -> c, where v is a
   * variable in sk_vars, and c is the term in n that it replaced. The flag
   * useConstantsAsHoles affects which terms we consider to be repairable.
   */
  Node getSkeleton(Node n,
                   std::map<TypeNode, int>& free_var_count,
                   std::vector<Node>& sk_vars,
                   std::map<Node, Node>& sk_vars_to_subs,
                   bool useConstantsAsHoles);
  /** get first-order query
   *
   * This function returns a formula that is equivalent to the negation of the
   * synthesis conjecture whose body is given in the first argument, where
   * candidates are replaced by candidate_skeletons,
   * whose free variables are in the set sk_vars. The returned formula
   * is a first-order (quantified) formula in the background logic, without UF,
   * of the form [***] above.
   */
  Node getFoQuery(Node body,
                  const std::vector<Node>& candidates,
                  const std::vector<Node>& candidate_skeletons,
                  const std::vector<Node>& sk_vars);
  /** fit to logic
   *
   * This function ensures that a query of the form [***] above fits the given
   * logic. In our approach for constant repair, replacing constants by
   * variables may introduce e.g. non-linearity. If non-linear arithmetic is
   * not enabled, we must undo some of the variables we introduced when
   * inferring candidate skeletons.
   *
   * body is the (sygus) form of the original synthesis conjecture we are
   * considering in this call.
   *
   * This function may remove variables from sk_vars and the map
   * sk_vars_to_subs. The skeletons candidate_skeletons are obtained by
   * getSkeleton(...) on the resulting vectors. If this function returns a
   * non-null node n', then n' is getFoQuery(...) on the resulting vectors, and
   * n' is in the given logic. The function may return null if it is not
   * possible to find a n' of this form.
   *
   * It uses the function below to choose which variables to remove from
   * sk_vars.
   */
  Node fitToLogic(Node body,
                  LogicInfo& logic,
                  Node n,
                  const std::vector<Node>& candidates,
                  std::vector<Node>& candidate_skeletons,
                  std::vector<Node>& sk_vars,
                  std::map<Node, Node>& sk_vars_to_subs);
  /** get fit to logic exclusion variable
   *
   * If n is not in the given logic, then this method either returns false,
   * or returns true and sets exvar to some variable in the domain of
   * d_fo_to_sk, that must be replaced by a constant for n to be in the given
   * logic. For example, for logic linear arithemic, for input:
   *    x * y = 5
   * where x is in the domain of d_fo_to_sk, this function returns true and sets
   * exvar to x.
   * If n is in the given logic, this method returns true.
   */
  bool getFitToLogicExcludeVar(LogicInfo& logic, Node n, Node& exvar);
  /** initialize checker
   *
   * This function initializes the smt engine checker to check the
   * satisfiability of the argument "query"
   *
   * The arguments em and varMap are used for supporting cases where we
   * want checker to use a different expression manager instead of the current
   * expression manager. The motivation for this so that different options can
   * be set for the subcall.
   *
   * We update the flag needExport to true if checker is using the expression
   * manager em. In this case, subsequent expressions extracted from smte
   * (for instance, model values) must be exported to the current expression
   * manager.
   */
  void initializeChecker(std::unique_ptr<SmtEngine>& checker,
                         ExprManager& em,
                         ExprManagerMapCollection& varMap,
                         Node query,
                         bool& needExport);
};

} /* CVC4::theory::quantifiers namespace */
} /* CVC4::theory namespace */
} /* CVC4 namespace */

#endif /* CVC4__THEORY__QUANTIFIERS__SYGUS_REPAIR_CONST_H */
