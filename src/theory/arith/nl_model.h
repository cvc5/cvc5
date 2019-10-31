/*********************                                                        */
/*! \file nl_model.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Model object for the non-linear extension class
 **/

#ifndef CVC4__THEORY__ARITH__NL_MODEL_H
#define CVC4__THEORY__ARITH__NL_MODEL_H

#include <map>
#include <unordered_map>
#include <vector>

#include "context/cdo.h"
#include "context/context.h"
#include "expr/kind.h"
#include "expr/node.h"
#include "theory/theory_model.h"

namespace CVC4 {
namespace theory {
namespace arith {

class NonlinearExtension;
  
/** Non-linear model
 *
 * TODO
 */
class NlModel
{
  friend class NonlinearExtension;
 public:
  NlModel(context::Context* c);
  ~NlModel();
  /** reset TODO */
  void reset(TheoryModel* m);
  /** reset check TODO */
  void resetCheck();
  /** compute model value
   *
   * This computes model values for terms based on two semantics, a "concrete"
   * semantics and an "abstract" semantics.
   *
   * index = 0 means compute the value of n based on its children recursively.
   *          (we call this its "concrete" value)
   * index = 1 means lookup the value of n in the model.
   *          (we call this its "abstract" value)
   * In other words, index = 1 treats multiplication terms and transcendental
   * function applications as variables, whereas index = 0 computes their
   * actual values. This is a key distinction used in the model-based
   * refinement scheme in Cimatti et al. TACAS 2017.
   *
   * For example, if M( a ) = 2, M( b ) = 3, M( a * b ) = 5, then :
   *
   *   computeModelValue( a*b, 0 ) =
   *   computeModelValue( a, 0 )*computeModelValue( b, 0 ) = 2*3 = 6
   * whereas:
   *   computeModelValue( a*b, 1 ) = 5
   */
  Node computeModelValue(Node n, unsigned index = 0);
  Node getAbstractModelValue(Node n) const;
  Node getConcreteModelValue(Node n) const;
  bool hasAbstractModelValue(Node n) const;
  bool hasConcreteModelValue(Node n) const;
  /** get computed model values
   * 
   * Returns the map of all computed concrete and abstract model values computed
   * by the above function.
   */
  std::map<Node, Node>& getConcreteModelValues();
  std::map<Node, Node>& getAbstractModelValues();
  std::map<Node, Node>& getModelValues(unsigned index);
  
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
  /** has check model assignment
   *
   * Have we assigned v in the current checkModel(...) call?
   *
   * This method returns true if variable v is in the domain of
   * d_check_model_bounds or if it occurs in d_check_model_vars.
   */
  bool hasCheckModelAssignment(Node v) const;
  /** set used approximate */
  void setUsedApproximate();
  /** did we use an approximation? */
  bool usedApproximate() const;
  //------------------------------ end recording model substitutions and bounds

  /** print model value, for debugging.
   * 
   * This prints both the abstract and concrete model values for arithmetic
   * term n on Trace c with precision prec.
   */
  void printModelValue(const char* c, Node n, unsigned prec = 5) const;
  /** record approximations in the current model
   * 
   * This makes necessary calls that notify the model of any approximations
   * that were used by this solver.
   */
  void recordApproximations();
 private:
  /** The current model */
  TheoryModel* d_model;
  /** TODO */
  Node getValueInternal(Node n) const;
  bool hasTerm(Node n) const;
  Node getRepresentative(Node n) const;
  
  Node getModelValueInternal(Node n, bool isConcrete) const;
  bool hasModelValueInternal(Node n, bool isConcrete) const;

  //---------------------------check model
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
                  const std::vector<Node>& false_asserts,
                  unsigned d,
                  std::vector<Node>& lemmas,
                  std::vector<Node>& gs
                 );

  /** solve equality simple
   *
   * This method is used during checkModel(...). It takes as input an
   * equality eq. If it returns true, then eq is correct-by-construction based
   * on the information stored in our model representation (see
   * d_check_model_vars, d_check_model_subs, d_check_model_bounds), and eq
   * is added to d_check_model_solved.
   */
  bool solveEqualitySimple(Node eq, unsigned d, std::vector<Node>& lemmas);

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

  /** is refinable transcendental function
   *
   * A transcendental function application is not refineable if its current
   * model value is zero, or if it is an application of SINE applied
   * to a non-variable.
   */
  bool isRefineableTfFun(Node tf);

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
  /*
  std::map< Node, Node > d_arithVal;
  std::map< Node, Node > d_valToRep;
  */
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
  std::map<Node, std::pair<Node, Node> > d_check_model_bounds;
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
}; /* class NlModel */

}  // namespace arith
}  // namespace theory
}  // namespace CVC4

#endif /* CVC4__THEORY__ARITH__NONLINEAR_EXTENSION_H */
