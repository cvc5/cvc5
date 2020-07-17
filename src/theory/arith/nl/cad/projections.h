
#ifndef CVC4__THEORY__NLARITH__CAD_PROJECTIONS_H
#define CVC4__THEORY__NLARITH__CAD_PROJECTIONS_H

#include <poly/polyxx.h>

#include <algorithm>
#include <iostream>
#include <vector>

namespace CVC4 {
namespace theory {
namespace arith {
namespace nl {
namespace cad {

/** Sort and remove duplicates from the list of polynomials. */
void reduce_projection_polynomials(std::vector<poly::Polynomial>& polys);

/**
 * Adds a polynomial to the list of projection polynomials.
 * Before adding, it factorizes the polynomials and removed constant factors.
 */
void add_polynomial(std::vector<poly::Polynomial>& polys,
                    const poly::Polynomial& poly);

/** Adds a list of polynomials using add_polynomial(). */
void add_polynomials(std::vector<poly::Polynomial>& polys,
                     const std::vector<poly::Polynomial>& p);

/** Make a set of polynomials a finest square-free basis. */
void make_finest_square_free_basis(std::vector<poly::Polynomial>& polys);

/** Ensure that two sets of polynomials are finest square-free basis relative to
 * each other. */
void make_finest_square_free_basis(std::vector<poly::Polynomial>& lhs,
                                   std::vector<poly::Polynomial>& rhs);

/**
 * Computes McCallum's projection operator.
 */
std::vector<poly::Polynomial> projection_mccallum(
    const std::vector<poly::Polynomial>& polys);

}  // namespace cad
}  // namespace nl
}  // namespace arith
}  // namespace theory
}  // namespace CVC4

#endif
