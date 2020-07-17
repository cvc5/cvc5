/*********************                                                        */
/*! \file nl_model.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Mathias Preiner
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Model object for the non-linear extension class
 **/

#ifndef CVC4__THEORY__ARITH__NL__NL_MODEL_H
#define CVC4__THEORY__ARITH__NL__NL_MODEL_H

#include <map>
#include <unordered_map>
#include <vector>

#include "context/cdo.h"
#include "context/context.h"
#include "expr/kind.h"
#include "expr/node.h"
#include "theory/arith/nl/nl_lemma_utils.h"
#include "theory/theory_model.h"

namespace CVC4 {
namespace theory {
namespace arith {
namespace nl {

class NonlinearExtension;

/** Non-linear model finder
 *
 * This class is responsible for all queries related to the (candidate) model
 * that is being processed by the non-linear arithmetic solver. It further
 * implements techniques for finding modifications to the current candidate
 * model in the case it can determine that a model exists. These include
 * techniques based on solving (quadratic) equations and bound analysis.
 */
class NlModel
{
  friend class NonlinearExtension;

 public:
  NlModel(context::Context* c);
  ~NlModel();
  /** reset
   *
   * This method is called once at the beginning of a last call effort check,
   * where m is the model of the theory of arithmetic. This method resets the
   * cache of computed model values.
   */
  void reset(TheoryModel* m, std::map<Node, Node>& arithModel);
  /** reset check
   *
   * This method is called when the non-linear arithmetic solver restarts
   * its computation of lemmas and models during a last call effort check.
   */
  void resetCheck();
  /** compute model value
   *
   * This computes model values for terms based on two semantics, a "concrete"
   * semantics and an "abstract" semantics.
   *
   * if isConcrete is true, this means compute the value of n based on its
   *          children recursively. (we call this its "concrete" value)
   * if isConcrete is false, this means lookup the value of n in the model.
   *          (we call this its "abstract" value)
   * In other words, !isConcrete treats multiplication terms and transcendental
   * function applications as variables, whereas isConcrete computes their
   * actual values based on the semantics of multiplication. This is a key
   * distinction used in the model-based refinement scheme in Cimatti et al.
   * TACAS 2017.
   *
   * For example, if M( a ) = 2, M( b ) = 3, M( a*b ) = 5, i.e. the variable
   * for a*b has been assigned a value 5 by the linear solver, then :
   *
   *   computeModelValue( a*b, true ) =
   *   computeModelValue( a, true )*computeModelValue( b, true ) = 2*3 = 6
   * whereas:
   *   computeModelValue( a*b, false ) = 5
   */
  Node computeConcreteModelValue(Node n);
  Node computeAbstractModelValue(Node n);
  Node computeModelValue(Node n, bool isConcrete);

  /** Compare arithmetic terms i and j based an ordering.
   *
   * This returns:
   *  -1 if i < j, 1 if i > j, or 0 if i == j
   *
   * If isConcrete is true, we consider the concrete model values of i and j,
   * otherwise, we consider their abstract model values. For definitions of
   * concrete vs abstract model values, see NlModel::computeModelValue.
   *
   * If isAbsolute is true, we compare the absolute value of thee above
   * values.
   */
  int compare(Node i, Node j, bool isConcrete, bool isAbsolute);
  /** Compare arithmetic terms i and j based an ordering.
   *
   * This returns:
   *  -1 if i < j, 1 if i > j, or 0 if i == j
   *
   * If isAbsolute is true, we compare the absolute value of i and j
   */
  int compareValue(Node i, Node j, bool isAbsolute) const;

  //------------------------------ recording model substitutions and bounds
  /** add check model substitution
   *
   * Adds the model substitution v -> s. This applies the substitution
   * { v -> s } to each term in d_check_model_subs and adds v,s to
   * d_check_model_vars and d_check_model_subs respectively.
   * If this method returns false, then the substitution v -> s is inconsistent
   * with the current substitution and bounds.
   */
  bool addCheckModelSubstitution(TNode v, TNode s);
  /** add check model bound
   *
   * Adds the bound x -> < l, u > to the map above, and records the
   * approximation ( x, l <= x <= u ) in the model. This method returns false
   * if the bound is inconsistent with the current model substitution or
   * bounds.
   */
  bool addCheckModelBound(TNode v, TNode l, TNode u);
  /** add check model witness
   *
   * Adds a model witness v -> w to the underlying theory model.
   * The witness should only contain a single variable v and evaluate to true
   * for exactly one value of v. The variable v is then (implicitly,
   * declaratively) assigned to this single value that satisfies the witness w.
   */
  bool addCheckModelWitness(TNode v, TNode w);
  /** has check model assignment
   *
   * Have we assigned v in the current checkModel(...) call?
   *
   * This method returns true if variable v is in the domain of
   * d_check_model_bounds or if it occurs in d_check_model_vars.
   */
  bool hasCheckModelAssignment(Node v) const;
  /** Check model
   *
   * Checks the current model based on solving for equalities, and using error
   * bounds on the Taylor approximation.
   *
   * If this function returns true, then all assertions in the input argument
   * "assertions" are satisfied for all interpretations of variables within
   * their computed bounds (as stored in d_check_model_bounds).
   *
   * For details, see Section 3 of Cimatti et al CADE 2017 under the heading
   * "Detecting Satisfiable Formulas".
   *
   * d is a degree indicating how precise our computations are.
   */
  bool checkModel(const std::vector<Node>& assertions,
                  unsigned d,
                  std::vector<NlLemma>& lemmas,
                  std::vector<Node>& gs);
  /**
   * Set that we have used an approximation during this check. This flag is
   * reset on a call to resetCheck. It is set when we use reasoning that
   * is limited by a degree of precision we are using. In other words, if we
   * used an approximation, then we maybe could still establish a lemma or
   * determine the input is SAT if we increased our precision.
   */
  void setUsedApproximate();
  /** Did we use an approximation during this check? */
  bool usedApproximate() const;
  /** Set tautology
   *
   * This states that formula n is a tautology (satisfied in all models).
   * We call this on internally generated lemmas. This method computes a
   * set of literals that are implied by n, that are hence tautological
   * as well, such as:
   *   l_pi <= real.pi <= u_pi (pi approximations)
   *   sin(x) = -1*sin(-x)
   * where these literals are internally generated for the purposes
   * of guiding the models of the linear solver.
   *
   * TODO (cvc4-projects #113: would be helpful if we could do this even
   * more aggressively by ignoring all internally generated literals.
   *
   * Tautological literals do not need be checked during checkModel.
   */
  void addTautology(Node n);
  //------------------------------ end recording model substitutions and bounds

  /** print model value, for debugging.
   *
   * This prints both the abstract and concrete model values for arithmetic
   * term n on Trace c with precision prec.
   */
  void printModelValue(const char* c, Node n, unsigned prec = 5) const;
  /** get model value repair
   *
   * This gets mappings that indicate how to repair the model generated by the
   * linear arithmetic solver. This method should be called after a successful
   * call to checkModel above.
   *
   * The mapping arithModel is updated by this method to map arithmetic terms v
   * to their (exact) value that was computed during checkModel; the mapping
   * approximations is updated to store approximate values in the form of a
   * pair (P, w), where P is a predicate that describes the possible values of
   * v and w is a witness point that satisfies this predicate.
   */
  void getModelValueRepair(
      std::map<Node, Node>& arithModel,
      std::map<Node, std::pair<Node, Node>>& approximations,
      std::map<Node, Node>& witnesses);

 private:
  /** The current model */
  TheoryModel* d_model;
  /** Get the model value of n from the model object above */
  Node getValueInternal(Node n) const;
  /** Does the equality engine of the model have term n? */
  bool hasTerm(Node n) const;
  /** Get the representative of n in the model */
  Node getRepresentative(Node n) const;

  //---------------------------check model
  /** solve equality simple
   *
   * This method is used during checkModel(...). It takes as input an
   * equality eq. If it returns true, then eq is correct-by-construction based
   * on the information stored in our model representation (see
   * d_check_model_vars, d_check_model_subs, d_check_model_bounds), and eq
   * is added to d_check_model_solved. The equality eq may involve any
   * number of variables, and monomials of arbitrary degree. If this method
   * returns false, then we did not show that the equality was true in the
   * model. This method uses incomplete techniques based on interval
   * analysis and quadratic equation solving.
   *
   * If it can be shown that the equality must be false in the current
   * model, then we may add a lemma to lemmas explaining why this is the case.
   * For instance, if eq reduces to a univariate quadratic equation with no
   * root, we send a conflict clause of the form a*x^2 + b*x + c != 0.
   */
  bool solveEqualitySimple(Node eq, unsigned d, std::vector<NlLemma>& lemmas);

  /** simple check model for transcendental functions for literal
   *
   * This method returns true if literal is true for all interpretations of
   * transcendental functions within their error bounds (as stored
   * in d_check_model_bounds). This is determined by a simple under/over
   * approximation of the value of sum of (linear) monomials. For example,
   * if we determine that .8 < sin( 1 ) < .9, this function will return
   * true for literals like:
   *   2.0*sin( 1 ) > 1.5
   *   -1.0*sin( 1 ) < -0.79
   *   -1.0*sin( 1 ) > -0.91
   *   sin( 1 )*sin( 1 ) + sin( 1 ) > 0.0
   * It will return false for literals like:
   *   sin( 1 ) > 0.85
   * It will also return false for literals like:
   *   -0.3*sin( 1 )*sin( 2 ) + sin( 2 ) > .7
   *   sin( sin( 1 ) ) > .5
   * since the bounds on these terms cannot quickly be determined.
   */
  bool simpleCheckModelLit(Node lit);
  bool simpleCheckModelMsum(const std::map<Node, Node>& msum, bool pol);
  //---------------------------end check model
  /** get approximate sqrt
   *
   * This approximates the square root of positive constant c. If this method
   * returns true, then l and u are updated to constants such that
   *   l <= sqrt( c ) <= u
   * The argument iter is the number of iterations in the binary search to
   * perform. By default, this is set to 15, which is usually enough to be
   * precise in the majority of simple cases, whereas not prohibitively
   * expensive to compute.
   */
  bool getApproximateSqrt(Node c, Node& l, Node& u, unsigned iter = 15) const;

  /** commonly used terms */
  Node d_zero;
  Node d_one;
  Node d_two;
  Node d_true;
  Node d_false;
  Node d_null;
  /**
   * The values that the arithmetic theory solver assigned in the model. This
   * corresponds to exactly the set of equalities that TheoryArith is currently
   * sending to TheoryModel during collectModelInfo.
   */
  std::map<Node, Node> d_arithVal;
  /** cache of model values
   *
   * Stores the the concrete/abstract model values. This is a cache of the
   * computeModelValue method.
   */
  std::map<Node, Node> d_mv[2];
  /**
   * A substitution from variables that appear in assertions to a solved form
   * term. These vectors are ordered in the form:
   *   x_1 -> t_1 ... x_n -> t_n
   * where x_i is not in the free variables of t_j for j>=i.
   */
  std::vector<Node> d_check_model_vars;
  std::vector<Node> d_check_model_subs;
  /** lower and upper bounds for check model
   *
   * For each term t in the domain of this map, if this stores the pair
   * (c_l, c_u) then the model M is such that c_l <= M( t ) <= c_u.
   *
   * We add terms whose value is approximated in the model to this map, which
   * includes:
   * (1) applications of transcendental functions, whose value is approximated
   * by the Taylor series,
   * (2) variables we have solved quadratic equations for, whose value
   * involves approximations of square roots.
   */
  std::map<Node, std::pair<Node, Node>> d_check_model_bounds;
  /** witnesses for check model
   *
   * Stores witnesses for vatiables that define implicit variable assignments.
   * For some variable v, we map to a formulas that is true for exactly one
   * value of v.
   */
  std::map<Node, Node> d_check_model_witnesses;
  /**
   * The map from literals that our model construction solved, to the variable
   * that was solved for. Examples of such literals are:
   * (1) Equalities x = t, which we turned into a model substitution x -> t,
   * where x not in FV( t ), and
   * (2) Equalities a*x*x + b*x + c = 0, which we turned into a model bound
   * -b+s*sqrt(b*b-4*a*c)/2a - E <= x <= -b+s*sqrt(b*b-4*a*c)/2a + E.
   *
   * These literals are exempt from check-model, since they are satisfied by
   * definition of our model construction.
   */
  std::unordered_map<Node, Node, NodeHashFunction> d_check_model_solved;
  /** did we use an approximation on this call to last-call effort? */
  bool d_used_approx;
  /** the set of all tautological literals */
  std::unordered_set<Node, NodeHashFunction> d_tautology;
}; /* class NlModel */

}  // namespace nl
}  // namespace arith
}  // namespace theory
}  // namespace CVC4

#endif /* CVC4__THEORY__ARITH__NONLINEAR_EXTENSION_H */
