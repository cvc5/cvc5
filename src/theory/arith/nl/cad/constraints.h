#ifndef CVC4__THEORY__NLARITH__CAD__CONSTRAINTS_H
#define CVC4__THEORY__NLARITH__CAD__CONSTRAINTS_H

#include <poly/polyxx.h>

#include <map>
#include <tuple>
#include <vector>

#include "../poly_conversion.h"
#include "expr/kind.h"
#include "expr/node_manager_attributes.h"

namespace CVC4 {
namespace theory {
namespace arith {
namespace nl {
namespace cad {

class Constraints
{
 public:
  /** Type alias for a list of constraints. */
  using Constraint = std::tuple<poly::Polynomial, poly::SignCondition, Node>;
  using ConstraintVector = std::vector<Constraint>;

 private:
  /** A list of constraints, each comprised of a polynomial and a sign
   * condition.
   */
  ConstraintVector mConstraints;

  /** A mapping from CVC4 variables to poly variables.
   */
  VariableMapper mVarMapper;

  void sort_constraints();

 public:
  VariableMapper& var_mapper() { return mVarMapper; }

  /** Add a constraing (represented by a polynomial and a sign condition) to the
   * list of constraints.
   */
  void add_constraint(const poly::Polynomial& lhs,
                      poly::SignCondition sc,
                      Node n);

  /** Add a constraints (represented by a node) to the list of constraints.
   * The given node can either be a negation (NOT) or a suitable relation symbol
   * as checked by is_suitable_relation().
   */
  void add_constraint(Node n);

  /** Gives the list of added constraints.
   */
  const ConstraintVector& get_constraints() const;

  /** Remove all constraints. */
  void reset();
};

}  // namespace cad
}  // namespace nl
}  // namespace arith
}  // namespace theory
}  // namespace CVC4

#endif