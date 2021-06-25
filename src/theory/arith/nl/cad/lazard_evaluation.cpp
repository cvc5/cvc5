#include "theory/arith/nl/cad/lazard_evaluation.h"

#ifdef CVC5_POLY_IMP

#include "base/check.h"
#include "base/output.h"
#include "smt/smt_statistics_registry.h"
#include "util/statistics_stats.h"

#ifdef CVC5_USE_COCOA

#include <CoCoA/library.H>

#include <optional>

namespace cvc5::theory::arith::nl::cad {

struct LazardEvaluationStats
{
  IntStat d_directAssignments =
      smtStatisticsRegistry().registerInt("theory::arith::cad::lazard-direct");
  IntStat d_ranAssignments =
      smtStatisticsRegistry().registerInt("theory::arith::cad::lazard-rans");
  IntStat d_evaluations =
      smtStatisticsRegistry().registerInt("theory::arith::cad::lazard-evals");
  IntStat d_reductions =
      smtStatisticsRegistry().registerInt("theory::arith::cad::lazard-reduce");
};

struct LazardEvaluationState;
std::ostream& operator<<(std::ostream& os, const LazardEvaluationState& state);

/**
 * This class holds and implements all the technicalities required to map
 * polynomials from libpoly into CoCoALib, perform these computations properly
 * within CoCoALib and map the result back to libpoly.
 *
 * We need to be careful to perform all computations in the proper polynomial
 * rings, both to be correct and because CoCoALib explicitly requires it. As we
 * change the ring we are computing it all the time, we also need appropriate
 * ring homomorphisms to map polynomials from one into the other. We first give
 * a short overview of our approach, then describe the various polynomial rings
 * that are used, and then discuss which rings are used where.
 *
 * Inputs:
 * - (real) variables x_0, ..., x_n
 * - real algebraic numbers a_0, ..., a_{n-1} with
 * - defining polynomials p_0, ..., p_{n-1}; p_i from Q[x_i]
 * - a polynomial q over all variables x_0, ..., x_n
 *
 * We first iteratively build the field extensions Q(a_0), Q(a_0, a_2) ...
 * Instead of the extension field Q(a_0), we use the isomorphic quotient ring
 * Q[x_0]/<p_0> and recursively extend it with a_1, etc, in the same way. Doing
 * this recursive construction naively fails: (Q[x_0]/<p_0>)[x_1]/<p_1> is not
 * necessarily a proper field as p_1 (though a minimal polynomial in Q[x_1]) may
 * factor over Q[x_0]/<p_0>. Consider p_0 = x_0*x_0-2 and p_1 =
 * x_1*x_1*x_1*x_1-2 as an example, where p_1 factors into
 * (x_1*x_1-x_0)*(x_1*x_1+x_0) over Q[x_0]/<p_0>. We overcome this by explicitly
 * computing this factorization and using the factor that vanishes over {x_0 ->
 * a_0, x_1 -> a_1 } as the minimal polynomial of a_1 over Q[x_0]/<p_0>.
 *
 * After we have built the field extensions in that way, we iteratively push q
 * through the field extensions, each one extended to a polynomial ring over all
 * x_0, ..., x_n. When in the k'th field extension, we check whether the k'th
 * minimal polynomial divides q. If so, q would vanish in the next step and we
 * instead set q = q/p_{k}. Only then we map q into K_{k+1}.
 *
 * Eventually, we end up with q in Q(a_0, ..., a_{n-1})[x_n]. This polynomial is
 * univariate conceptually, and we want to compute its roots. However, it is not
 * technically univariate and we need to make it so. We can do this by computing
 * the Gröbner basis of the q and all minimal polynomials p_i with an
 * elimination order with x_n at the bottom over Q[x_0, ..., x_n].
 * We then collect the polynomials
 * that are univariate in x_n from the Gröbner basis. We can show that the roots
 * of these polynomials are a superset of the roots we are looking for.
 *
 *
 * To implement all that, we construct the following polynomial rings:
 * - K_i: K_0 = Q, K_{i+1} = K_{i}[x_i]/<p_i> (with p_i reduced w.r.t. K_i)
 * - R_i = K_i[x_i]
 * - J_i = K_i[x_i, ..., x_n] = R_i[x_{i+1}, ..., x_n]
 *
 * While p_i conceptually live in Q[x_i], we immediately convert them from
 * libpoly into R_i. We then factor it there, obtaining the actual minimal
 * polynomial p_i that we use to construct K_{i+1}. We do this to construct all
 * K_i and R_i. We then reduce q, initially in Q[x_0, ..., x_n] = J_0. We check
 * in J_i whether p_i divides q (and if so divide q by p_i). To do
 * this, we need to embed p_i into J_i. We then
 * map q from J_i to J_{i+1}. While obvious in theory, this is somewhat tricky
 * in practice as J_i and J_{i+1} have no direct relationship.
 * Finally, we need to push all p_i and the final q back into J_0 = Q[x_0, ...,
 * x_n] to compute the Gröbner basis.
 *
 * We thus furthermore store the following ring homomorphisms:
 * - phom_i: R_i -> J_i (canonical embedding)
 * - qhom_i: J_i -> J_{i+1} (hand-crafted homomorphism)
 *
 * We can sometimes avoid this construction for individual variables, i.e., if
 * the assignment for x_i already lives (algebraically) in K_i. This can be the
 * case if a_i is rational; in general, we check whether the vanishing factor
 * of p_i is linear. If so, it has the form x_i-r where is some term in lower
 * variables. We store r as the "direct assignment" in d_direct[i] and use it
 * to directly replace x_i when appropriate. Also, we have K_i = K_{i-1}.
 *
 */
struct LazardEvaluationState
{
  CoCoA::GlobalManager d_gm;
  static std::unique_ptr<LazardEvaluationStats> d_stats;

  /**
   * Maps libpoly variables to indets in J0. Used when constructing the input
   * polynomial q in the first polynomial ring J0.
   */
  std::map<poly::Variable, CoCoA::RingElem> d_varQ;
  /**
   * Maps CoCoA indets back to to libpoly variables.
   * Use when converting CoCoA RingElems to libpoly polynomials, either when
   * checking whether a factor vanishes or when returning the univariate
   * elements of the final Gröbner basis. The CoCoA indets are identified by the
   * pair of the ring id and the indet identifier. Hence, we can put all of them
   * in one map, no matter which ring they belong to.
   */
  std::map<std::pair<long, size_t>, poly::Variable> d_varCoCoA;

  /**
   * The minimal polynomials p_i used for constructing d_K.
   * If a variable x_i has a rational assignment, p_i holds no value (i.e.
   * d_p[i] == CoCoA::RingElem()).
   */
  std::vector<CoCoA::RingElem> d_p;

  /**
   * The sequence of extension fields.
   * K_0 = Q, K_{i+1} = K_i[x_i]/<p_i>
   * Every K_i is a field.
   */
  std::vector<CoCoA::ring> d_K = {CoCoA::RingQQ()};
  /**
   * R_i = K_i[x_i]
   * Every R_i is a univariate polynomial ring over the field K_i.
   */
  std::vector<CoCoA::ring> d_R;
  /**
   * J_i = K_i[x_i, ..., x_n]
   * All J_i are constructed with CoCoA::lex ordering, just to make sure that
   * the Gröbner basis of J_0 is computed as necessary.
   */
  std::vector<CoCoA::ring> d_J;

  /**
   * Custom homomorphism from R_i to J_i. PolyAlgebraHom with
   * Indets(R_i) = (x_i) --> (x_i)
   */
  std::vector<CoCoA::RingHom> d_phom;
  /**
   * Custom homomorphism from J_i to J_{i+1}
   * If assignment of x_i is rational a PolyAlgebraHom with
   * Indets(J_i) = (x_i,...,x_n) --> (a_i,x_{i+1},...,x_n)
   * Otherwise a PolyRingHom with:
   * - CoeffHom: K_{i-1} --> R_{i-1} --> K_i
   * - (x_i,...,x_n) --> (x_i,x_{i+1},...,x_n), x_i = Indet(R_{i-1})
   */
  std::vector<CoCoA::RingHom> d_qhom;

  /**
   * The base ideal for the Gröbner basis we compute in the end. Contains all
   * p_i pushed into J_0.
   */
  std::vector<CoCoA::RingElem> d_GBBaseIdeal;

  /**
   * The current assignment, used to identify the vanishing factor to construct
   * K_i.
   */
  poly::Assignment d_assignment;
  /**
   * The libpoly variables in proper order. Directly correspond to x_0,...,x_n.
   */
  std::vector<poly::Variable> d_variables;
  /**
   * Direct assignments for variables x_i as polynomials in lower variables.
   * If the assignment for x_i is no direct assignment, d_direct[i] holds no
   * value.
   */
  std::vector<std::optional<CoCoA::RingElem>> d_direct;

  LazardEvaluationState()
  {
    if (!d_stats)
    {
      d_stats = std::make_unique<LazardEvaluationStats>();
    }
  }

  /**
   * Converts a libpoly integer to a CoCoA::BigInt.
   */
  CoCoA::BigInt convert(const poly::Integer& i) const
  {
    return CoCoA::BigIntFromMPZ(poly::detail::cast_to_gmp(&i)->get_mpz_t());
  }
  /**
   * Converts a libpoly dyadic rational to a CoCoA::BigRat.
   */
  CoCoA::BigRat convert(const poly::DyadicRational& dr) const
  {
    return CoCoA::BigRat(convert(poly::numerator(dr)),
                         convert(poly::denominator(dr)));
  }
  /**
   * Converts a libpoly rational to a CoCoA::BigRat.
   */
  CoCoA::BigRat convert(const poly::Rational& r) const
  {
    return CoCoA::BigRatFromMPQ(poly::detail::cast_to_gmp(&r)->get_mpq_t());
  }
  /**
   * Converts a univariate libpoly polynomial p in variable var to CoCoA. It
   * assumes that p is a minimal polynomial p_i over variable x_i for the
   * highest variable x_i known yet. It thus directly constructs p_i in R_i.
   */
  CoCoA::RingElem convertMiPo(const poly::UPolynomial& p,
                              const poly::Variable& var) const
  {
    std::vector<poly::Integer> coeffs = poly::coefficients(p);
    CoCoA::RingElem res(d_R.back());
    CoCoA::RingElem v = CoCoA::indet(d_R.back(), 0);
    CoCoA::RingElem mult(d_R.back(), 1);
    for (const auto& c : coeffs)
    {
      if (!poly::is_zero(c))
      {
        res += convert(c) * mult;
      }
      mult *= v;
    }
    return res;
  }

  /**
   * Checks whether the given CoCoA polynomial evaluates to zero over the
   * current libpoly assignment. The polynomial should live over the current
   * R_i.
   */
  bool evaluatesToZero(const CoCoA::RingElem& cp) const
  {
    Assert(CoCoA::owner(cp) == d_R.back());
    poly::Polynomial pp = convert(cp);
    return poly::evaluate_constraint(pp, d_assignment, poly::SignCondition::EQ);
  }

  /**
   * Maps p from J_i to J_{i-1}. There can be no suitable homomorphism, and we
   * thus manually decompose p into its terms and reconstruct them in J_{i-1}.
   * If a_{i-1} is rational, we know that the coefficient rings of J_i and
   * J_{i-1} are identical (K_{i-1} and K_{i-2}, respectively). We can thus
   * immediately use coefficients from J_i as coefficients in J_{i-1}.
   * Otherwise, we map coefficients from K_{i-1} to their canonical
   * representation in R_{i-1} and then use d_phom[i-1] to map those into
   * J_{i-1}. Afterwards, we iterate over the power product of the term
   * reconstruct it in J_{i-1}.
   */
  CoCoA::RingElem pushDownJ(const CoCoA::RingElem& p, size_t i) const
  {
    Trace("cad::lazard") << "Push " << p << " from " << d_J[i] << " to "
                         << d_J[i - 1] << std::endl;
    Assert(CoCoA::owner(p) == d_J[i]);
    CoCoA::RingElem res(d_J[i - 1]);
    for (CoCoA::SparsePolyIter it = CoCoA::BeginIter(p); !CoCoA::IsEnded(it);
         ++it)
    {
      CoCoA::RingElem coeff = CoCoA::coeff(it);
      Assert(CoCoA::owner(coeff) == d_K[i]);
      if (d_direct[i - 1])
      {
        Assert(CoCoA::CoeffRing(d_J[i]) == CoCoA::CoeffRing(d_J[i - 1]));
        coeff = CoCoA::CoeffEmbeddingHom(d_J[i - 1])(coeff);
      }
      else
      {
        coeff = CoCoA::CanonicalRepr(coeff);
        Assert(CoCoA::owner(coeff) == d_R[i - 1]);
        coeff = d_phom[i - 1](coeff);
      }
      Assert(CoCoA::owner(coeff) == d_J[i - 1]);
      auto pp = CoCoA::PP(it);
      std::vector<long> indets = CoCoA::IndetsIn(pp);
      for (size_t k = 0; k < indets.size(); ++k)
      {
        long exp = CoCoA::exponent(pp, indets[k]);
        auto ind = CoCoA::indet(d_J[i - 1], indets[k] + 1);
        coeff *= CoCoA::power(ind, exp);
      }
      res += coeff;
    }
    return res;
  }

  /**
   * Uses pushDownJ repeatedly to map p from J_{i+1} to J_0.
   * Is used to map the minimal polynomials p_i and the reduced polynomial q
   * into J_0 to eventually compute the Gröbner basis.
   */
  CoCoA::RingElem pushDownJ0(const CoCoA::RingElem& p, size_t i) const
  {
    CoCoA::RingElem res = p;
    for (; i > 0; --i)
    {
      Trace("cad::lazard") << "Pushing " << p << " from J" << i << " to J"
                           << i - 1 << std::endl;
      res = pushDownJ(res, i);
    }
    return res;
  }

  /**
   * Add the next R_i:
   * - add variable x_i to d_variables
   * - extract the variable name
   * - construct R_i = K_i[x_i]
   * - add new variable to d_varCoCoA
   */
  void addR(const poly::Variable& var)
  {
    d_variables.emplace_back(var);
    if (Trace.isOn("cad::lazard"))
    {
      std::string vname = lp_variable_db_get_name(
          poly::Context::get_context().get_variable_db(), var.get_internal());
      d_R.emplace_back(CoCoA::NewPolyRing(d_K.back(), {CoCoA::symbol(vname)}));
    }
    else
    {
      d_R.emplace_back(CoCoA::NewPolyRing(d_K.back(), {CoCoA::NewSymbol()}));
    }
    Trace("cad::lazard") << "R" << d_R.size() - 1 << " = " << d_R.back()
                         << std::endl;
    d_varCoCoA.emplace(std::make_pair(CoCoA::RingID(d_R.back()), 0), var);
  }

  /**
   * Add the next K_{i+1} from a minimal polynomial:
   * - store dummy value in d_direct
   * - store the minimal polynomial p_i in d_p
   * - construct K_{i+1} = R_i/<p_i>
   */
  void addK(const poly::Variable& var, const CoCoA::RingElem& p)
  {
    d_direct.emplace_back();
    d_p.emplace_back(p);
    Trace("cad::lazard") << "p" << d_p.size() - 1 << " = " << d_p.back()
                         << std::endl;
    d_K.emplace_back(CoCoA::NewQuotientRing(d_R.back(), CoCoA::ideal(p)));
    Trace("cad::lazard") << "K" << d_K.size() - 1 << " = " << d_K.back()
                         << std::endl;
  }

  /**
   * Add the next K_{i+1} from a rational assignment:
   * - store assignment a_i in d_direct
   * - store a dummy minimal polynomial in d_p
   * - construct K_{i+1} as copy of K_i
   */
  void addKRational(const poly::Variable& var, const CoCoA::RingElem& r)
  {
    d_direct.emplace_back(r);
    d_p.emplace_back();
    Trace("cad::lazard") << "x" << d_p.size() - 1 << " = " << r << std::endl;
    d_K.emplace_back(d_K.back());
    Trace("cad::lazard") << "K" << d_K.size() - 1 << " = " << d_K.back()
                         << std::endl;
  }

  /**
   * Finish the whole construction by adding the free variable:
   * - add R_n by calling addR(var)
   * - construct all J_i
   * - construct all p homomorphisms (R_i --> J_i)
   * - construct all q homomorphisms (J_i --> J_{i+1})
   * - fill the mapping d_varQ (libpoly -> J_0)
   * - fill the mapping d_varCoCoA (J_n -> libpoly)
   * - fill d_GBBaseIdeal with p_i mapped to J_0
   */
  void addFreeVariable(const poly::Variable& var)
  {
    Trace("cad::lazard") << "Add free variable " << var << std::endl;
    addR(var);
    std::vector<CoCoA::symbol> symbols;
    for (size_t i = 0; i < d_R.size(); ++i)
    {
      symbols.emplace_back(CoCoA::symbols(d_R[i]).back());
    }
    for (size_t i = 0; i < d_R.size(); ++i)
    {
      d_J.emplace_back(CoCoA::NewPolyRing(d_K[i], symbols, CoCoA::lex));
      Trace("cad::lazard") << "J" << d_J.size() - 1 << " = " << d_J.back()
                           << std::endl;
      symbols.erase(symbols.begin());
      // R_i --> J_i
      d_phom.emplace_back(
          CoCoA::PolyAlgebraHom(d_R[i], d_J[i], {CoCoA::indet(d_J[i], 0)}));
      Trace("cad::lazard") << "R" << i << " --> J" << i << ": " << d_phom.back()
                           << std::endl;
      if (i > 0)
      {
        Trace("cad::lazard")
            << "Constructing J" << i - 1 << " --> J" << i << ": " << std::endl;
        Trace("cad::lazard") << "Constructing " << d_J[i - 1] << " --> "
                             << d_J[i] << ": " << std::endl;
        if (d_direct[i - 1])
        {
          Trace("cad::lazard") << "Using " << d_variables[i - 1] << " for "
                               << CoCoA::indet(d_J[i - 1], 0) << std::endl;
          Assert(CoCoA::CoeffRing(d_J[i]) == CoCoA::owner(*d_direct[i - 1]));
          std::vector<CoCoA::RingElem> indets = {
              CoCoA::RingElem(d_J[i], *d_direct[i - 1])};
          for (size_t j = 0; j < d_R.size() - i; ++j)
          {
            indets.push_back(CoCoA::indet(d_J[i], j));
          }
          d_qhom.emplace_back(
              CoCoA::PolyAlgebraHom(d_J[i - 1], d_J[i], indets));
        }
        else
        {
          // K_{i-1} --> R_{i-1}
          auto K2R = CoCoA::CoeffEmbeddingHom(d_R[i - 1]);
          Assert(CoCoA::domain(K2R) == d_K[i - 1]);
          Assert(CoCoA::codomain(K2R) == d_R[i - 1]);
          // R_{i-1} --> K_i
          auto R2K = CoCoA::QuotientingHom(d_K[i]);
          Assert(CoCoA::domain(R2K) == d_R[i - 1]);
          Assert(CoCoA::codomain(R2K) == d_K[i]);
          // K_i --> J_i
          auto K2J = CoCoA::CoeffEmbeddingHom(d_J[i]);
          Assert(CoCoA::domain(K2J) == d_K[i]);
          Assert(CoCoA::codomain(K2J) == d_J[i]);
          // J_{i-1} --> J_i, consisting of
          // - a homomorphism for the coefficients
          // - a mapping for the indets
          // Constructs [phom_i(x_i), x_i+1, ..., x_n]
          std::vector<CoCoA::RingElem> indets = {
              K2J(R2K(CoCoA::indet(d_R[i - 1], 0)))};
          for (size_t j = 0; j < d_R.size() - i; ++j)
          {
            indets.push_back(CoCoA::indet(d_J[i], j));
          }
          d_qhom.emplace_back(
              CoCoA::PolyRingHom(d_J[i - 1], d_J[i], R2K(K2R), indets));
        }
        Trace("cad::lazard") << "J" << i - 1 << " --> J" << i << ": "
                             << d_qhom.back() << std::endl;
      }
    }
    for (size_t i = 0; i < d_variables.size(); ++i)
    {
      d_varQ.emplace(d_variables[i], CoCoA::indet(d_J[0], i));
    }
    for (size_t i = 0; i < d_variables.size(); ++i)
    {
      d_varCoCoA.emplace(std::make_pair(CoCoA::RingID(d_J[0]), i),
                         d_variables[i]);
    }

    d_GBBaseIdeal.clear();
    for (size_t i = 0; i < d_p.size(); ++i)
    {
      if (d_direct[i]) continue;
      Trace("cad::lazard") << "Apply " << d_phom[i] << " to " << d_p[i]
                           << " from " << CoCoA::owner(d_p[i]) << std::endl;
      d_GBBaseIdeal.emplace_back(pushDownJ0(d_phom[i](d_p[i]), i));
    }

    Trace("cad::lazard") << "Finished construction" << std::endl
                         << *this << std::endl;
  }

  /**
   * Helper class for conversion from libpoly to CoCoA polynomials.
   * The lambda can not capture anything, as it needs to be of type
   * lp_polynomial_traverse_f.
   */
  struct CoCoAPolyConstructor
  {
    const LazardEvaluationState& d_state;
    CoCoA::RingElem d_result;
  };

  /**
   * Convert the polynomial q to CoCoA into J_0.
   */
  CoCoA::RingElem convertQ(const poly::Polynomial& q) const
  {
    CoCoAPolyConstructor cmd{*this};
    // Do the actual conversion
    cmd.d_result = CoCoA::RingElem(d_J[0]);
    lp_polynomial_traverse_f f = [](const lp_polynomial_context_t* ctx,
                                    lp_monomial_t* m,
                                    void* data) {
      CoCoAPolyConstructor* d = static_cast<CoCoAPolyConstructor*>(data);
      CoCoA::BigInt coeff = d->d_state.convert(*poly::detail::cast_from(&m->a));
      CoCoA::RingElem re(d->d_state.d_J[0], coeff);
      for (size_t i = 0; i < m->n; ++i)
      {
        // variable exponent pair
        CoCoA::RingElem var = d->d_state.d_varQ.at(m->p[i].x);
        re *= CoCoA::power(var, m->p[i].d);
      }
      d->d_result += re;
    };
    lp_polynomial_traverse(q.get_internal(), f, &cmd);
    return cmd.d_result;
  }
  /**
   * Actual (recursive) implementation of converting a CoCoA polynomial to a
   * libpoly polynomial. As libpoly polynomials only have integer coefficients,
   * we need to maintain an integer denominator to normalize all terms to the
   * same denominator.
   */
  poly::Polynomial convertImpl(const CoCoA::RingElem& p,
                               poly::Integer& denominator) const
  {
    Trace("cad::lazard") << "Converting " << p << std::endl;
    denominator = poly::Integer(1);
    poly::Polynomial res;
    for (CoCoA::SparsePolyIter i = CoCoA::BeginIter(p); !CoCoA::IsEnded(i); ++i)
    {
      poly::Polynomial coeff;
      poly::Integer denom(1);
      CoCoA::BigRat numcoeff;
      if (CoCoA::IsRational(numcoeff, CoCoA::coeff(i)))
      {
        poly::Rational rat(mpq_class(CoCoA::mpqref(numcoeff)));
        denom = poly::denominator(rat);
        coeff = poly::numerator(rat);
      }
      else
      {
        coeff = convertImpl(CoCoA::CanonicalRepr(CoCoA::coeff(i)), denom);
      }
      if (!CoCoA::IsOne(CoCoA::PP(i)))
      {
        std::vector<long> exponents;
        CoCoA::exponents(exponents, CoCoA::PP(i));
        for (size_t vid = 0; vid < exponents.size(); ++vid)
        {
          if (exponents[vid] == 0) continue;
          const auto& ring = CoCoA::owner(p);
          poly::Variable v =
              d_varCoCoA.at(std::make_pair(CoCoA::RingID(ring), vid));
          coeff *= poly::Polynomial(poly::Integer(1), v, exponents[vid]);
        }
      }
      if (denom != denominator)
      {
        poly::Integer g = gcd(denom, denominator);
        res = res * (denom / g) + coeff * (denominator / g);
        denominator *= (denom / g);
      }
      else
      {
        res += coeff;
      }
    }
    Trace("cad::lazard") << "-> " << res << std::endl;
    return res;
  }
  /**
   * Actually convert a CoCoA RingElem to a libpoly polynomial.
   * Requires d_varCoCoA to be filled appropriately.
   */
  poly::Polynomial convert(const CoCoA::RingElem& p) const
  {
    poly::Integer denom;
    return convertImpl(p, denom);
  }

  /**
   * Now reduce the polynomial qpoly:
   * - convert qpoly into J_0 and factor it
   * - for every factor q:
   *   - for every x_i:
   *     - if a_i is rational:
   *       - while q[x_i -> a_i] == 0
   *         - q = q / (x_i - a_i)
   *       - set q = q[x_i -> a_i]
   *     - otherwise
   *       - obtain tmp = phom_i(p_i)
   *       - while tmp divides q
   *         - q = q / tmp
   *     - embed q = qhom_i(q)
   * - compute (reduced) GBasis(p_0, ..., p_{n-i}, q)
   * - collect and convert basis elements univariate in the free variable
   */
  std::vector<poly::Polynomial> reduce(const poly::Polynomial& qpoly) const
  {
    d_stats->d_evaluations++;
    std::vector<poly::Polynomial> res;
    Trace("cad::lazard") << "Reducing " << qpoly << std::endl;
    auto input = convertQ(qpoly);
    Assert(CoCoA::owner(input) == d_J[0]);
    auto factorization = CoCoA::factor(input);
    for (const auto& f : factorization.myFactors())
    {
      Trace("cad::lazard") << "-> factor " << f << std::endl;
      CoCoA::RingElem q = f;
      for (size_t i = 0; i < d_J.size() - 1; ++i)
      {
        Trace("cad::lazard") << "i = " << i << std::endl;
        if (d_direct[i])
        {
          Trace("cad::lazard")
              << "Substitute " << d_variables[i] << " = " << *d_direct[i]
              << " into " << q << " from " << CoCoA::owner(q) << std::endl;
          auto indets = CoCoA::indets(d_J[i]);
          auto var = indets[0];
          Assert(CoCoA::CoeffRing(d_J[i]) == CoCoA::owner(*d_direct[i]));
          indets[0] = CoCoA::RingElem(d_J[i], *d_direct[i]);
          auto hom = CoCoA::PolyAlgebraHom(d_J[i], d_J[i], indets);
          while (CoCoA::IsZero(hom(q)))
          {
            q = q / (var - indets[0]);
            d_stats->d_reductions++;
          }
          // substitute x_i -> a_i
          q = hom(q);
          Trace("cad::lazard")
              << "-> " << q << " from " << CoCoA::owner(q) << std::endl;
        }
        else
        {
          auto tmp = d_phom[i](d_p[i]);
          while (CoCoA::IsDivisible(q, tmp))
          {
            q /= tmp;
            d_stats->d_reductions++;
          }
        }
        q = d_qhom[i](q);
      }
      Trace("cad::lazard") << "-> reduced to " << q << std::endl;
      Assert(CoCoA::owner(q) == d_J.back());
      std::vector<CoCoA::RingElem> ideal = d_GBBaseIdeal;
      ideal.emplace_back(pushDownJ0(q, d_J.size() - 1));
      Trace("cad::lazard") << "-> ideal " << ideal << std::endl;
      auto basis = CoCoA::ReducedGBasis(CoCoA::ideal(ideal));
      Trace("cad::lazard") << "-> basis " << basis << std::endl;
      for (const auto& belem : basis)
      {
        Trace("cad::lazard") << "-> retrieved " << belem << std::endl;
        auto pres = convert(belem);
        Trace("cad::lazard") << "-> converted " << pres << std::endl;
        // These checks are orthogonal!
        if (poly::is_univariate(pres)
            && poly::is_univariate_over_assignment(pres, d_assignment))
        {
          res.emplace_back(pres);
        }
      }
    }
    return res;
  }
};

std::ostream& operator<<(std::ostream& os, const LazardEvaluationState& state)
{
  for (size_t i = 0; i < state.d_K.size(); ++i)
  {
    os << "K" << i << " = " << state.d_K[i] << std::endl;
    os << "R" << i << " = " << state.d_R[i] << std::endl;
    os << "J" << i << " = " << state.d_J[i] << std::endl;

    os << "R" << i << " --> J" << i << ": " << state.d_phom[i] << std::endl;
    if (i > 0)
    {
      os << "J" << (i - 1) << " --> J" << i << ": " << state.d_qhom[i - 1]
         << std::endl;
    }
  }
  os << "GBBaseIdeal: " << state.d_GBBaseIdeal << std::endl;
  os << "Done" << std::endl;
  return os;
}
std::unique_ptr<LazardEvaluationStats> LazardEvaluationState::d_stats;

LazardEvaluation::LazardEvaluation()
    : d_state(std::make_unique<LazardEvaluationState>())
{
}

LazardEvaluation::~LazardEvaluation() {}

/**
 * Add a new variable with real algebraic number:
 * - add var = ran to the assignment
 * - add the next R_i by calling addR(var)
 * - if ran is actually rational:
 *   - obtain the rational and call addKRational()
 * - otherwise:
 *   - convert the minimal polynomial and identify vanishing factor
 *   - add the next K_i with the vanishing factor by valling addK()
 */
void LazardEvaluation::add(const poly::Variable& var, const poly::Value& val)
{
  Trace("cad::lazard") << "Adding " << var << " -> " << val << std::endl;
  try
  {
    d_state->d_assignment.set(var, val);
    d_state->addR(var);

    std::optional<CoCoA::BigRat> rational;
    poly::UPolynomial polymipo;
    if (poly::is_algebraic_number(val))
    {
      const poly::AlgebraicNumber& ran = poly::as_algebraic_number(val);
      const poly::DyadicInterval& di = poly::get_isolating_interval(ran);
      if (poly::is_point(di))
      {
        rational = d_state->convert(poly::get_point(di));
      }
      else
      {
        Trace("cad::lazard") << "\tis proper ran" << std::endl;
        polymipo = poly::get_defining_polynomial(ran);
      }
    }
    else
    {
      Assert(poly::is_dyadic_rational(val) || poly::is_integer(val)
             || poly::is_rational(val));
      if (poly::is_dyadic_rational(val))
      {
        rational = d_state->convert(poly::as_dyadic_rational(val));
      }
      else if (poly::is_integer(val))
      {
        rational = CoCoA::BigRat(d_state->convert(poly::as_integer(val)), 1);
      }
      else if (poly::is_rational(val))
      {
        rational = d_state->convert(poly::as_rational(val));
      }
    }

    if (rational)
    {
      d_state->addKRational(var,
                            CoCoA::RingElem(d_state->d_K.back(), *rational));
      d_state->d_stats->d_directAssignments++;
      return;
    }
    Trace("cad::lazard") << "Got mipo " << polymipo << std::endl;
    auto mipo = d_state->convertMiPo(polymipo, var);
    Trace("cad::lazard") << "Factoring " << mipo << " from "
                         << CoCoA::owner(mipo) << std::endl;
    auto factorization = CoCoA::factor(mipo);
    Trace("cad::lazard") << "-> " << factorization << std::endl;
    bool used_factor = false;
    for (const auto& f : factorization.myFactors())
    {
      if (d_state->evaluatesToZero(f))
      {
        Assert(CoCoA::deg(f) > 0 && CoCoA::NumTerms(f) <= 2);
        if (CoCoA::deg(f) == 1)
        {
          auto rat = -CoCoA::ConstantCoeff(f) / CoCoA::LC(f);
          Trace("cad::lazard") << "Using linear factor " << f << " -> " << var
                               << " = " << rat << std::endl;
          d_state->addKRational(var, rat);
          d_state->d_stats->d_directAssignments++;
        }
        else
        {
          Trace("cad::lazard") << "Using nonlinear factor " << f << std::endl;
          d_state->addK(var, f);
          d_state->d_stats->d_ranAssignments++;
        }
        used_factor = true;
        break;
      }
      else
      {
        Trace("cad::lazard") << "Skipping " << f << std::endl;
      }
    }
    Assert(used_factor);
  }
  catch (CoCoA::ErrorInfo& e)
  {
    e.myOutputSelf(std::cerr);
    throw;
  }
}

void LazardEvaluation::addFreeVariable(const poly::Variable& var)
{
  try
  {
    d_state->addFreeVariable(var);
  }
  catch (CoCoA::ErrorInfo& e)
  {
    e.myOutputSelf(std::cerr);
    throw;
  }
}

std::vector<poly::Polynomial> LazardEvaluation::reducePolynomial(
    const poly::Polynomial& p) const
{
  try
  {
    return d_state->reduce(p);
  }
  catch (CoCoA::ErrorInfo& e)
  {
    e.myOutputSelf(std::cerr);
    throw;
  }
  return {p};
}

/**
 * Compute the infeasible regions of the given polynomial according to a sign
 * condition. We first reduce the polynomial and isolate the real roots of every
 * resulting polynomial. We store all roots (except for -infty, +infty and none)
 * in a set. Then, we transform the set of roots into a list of infeasible
 * regions by generating intervals between -infty and the first root, in between
 * every two consecutive roots and between the last root and +infty. While doing
 * this, we only keep those intervals that are actually infeasible for the
 * original polynomial q over the partial assignment. Finally, we go over the
 * intervals and aggregate consecutive intervals that connect.
 */
std::vector<poly::Interval> LazardEvaluation::infeasibleRegions(
    const poly::Polynomial& q, poly::SignCondition sc) const
{
  poly::Assignment a;
  std::set<poly::Value> roots;
  // reduce q to a set of reduced polynomials p
  for (const auto& p : reducePolynomial(q))
  {
    // collect all real roots except for -infty, none, +infty
    Trace("cad::lazard") << "Isolating roots of " << p << std::endl;
    Assert(poly::is_univariate(p) && poly::is_univariate_over_assignment(p, a));
    std::vector<poly::Value> proots = poly::isolate_real_roots(p, a);
    for (const auto& r : proots)
    {
      if (poly::is_minus_infinity(r)) continue;
      if (poly::is_none(r)) continue;
      if (poly::is_plus_infinity(r)) continue;
      roots.insert(r);
    }
  }

  // generate all intervals
  // (-infty,root_0), [root_0], (root_0,root_1), ..., [root_m], (root_m,+infty)
  // if q is true over d_assignment x interval (represented by a sample)
  std::vector<poly::Interval> res;
  poly::Value last = poly::Value::minus_infty();
  for (const auto& r : roots)
  {
    poly::Value sample = poly::value_between(last, true, r, true);
    d_state->d_assignment.set(d_state->d_variables.back(), sample);
    if (!poly::evaluate_constraint(q, d_state->d_assignment, sc))
    {
      res.emplace_back(last, true, r, true);
    }
    d_state->d_assignment.set(d_state->d_variables.back(), r);
    if (!poly::evaluate_constraint(q, d_state->d_assignment, sc))
    {
      res.emplace_back(r);
    }
    last = r;
  }
  poly::Value sample =
      poly::value_between(last, true, poly::Value::plus_infty(), true);
  d_state->d_assignment.set(d_state->d_variables.back(), sample);
  if (!poly::evaluate_constraint(q, d_state->d_assignment, sc))
  {
    res.emplace_back(last, true, poly::Value::plus_infty(), true);
  }
  // clean up assignment
  d_state->d_assignment.unset(d_state->d_variables.back());

  Trace("cad::lazard") << "Shrinking:" << std::endl;
  for (const auto& i : res)
  {
    Trace("cad::lazard") << "-> " << i << std::endl;
  }
  std::vector<poly::Interval> combined;
  if (res.empty())
  {
    // nothing to do if there are no intervals to start with
    // return combined to simplify return value optimization
    return combined;
  }
  for (size_t i = 0; i < res.size() - 1; ++i)
  {
    // Invariant: the intervals do not overlap. Check for our own sanity.
    Assert(poly::get_upper(res[i]) <= poly::get_lower(res[i + 1]));
    if (poly::get_upper_open(res[i]) && poly::get_lower_open(res[i + 1]))
    {
      // does not connect, both are open
      combined.emplace_back(res[i]);
      continue;
    }
    if (poly::get_upper(res[i]) != poly::get_lower(res[i + 1]))
    {
      // does not connect, there is some space in between
      combined.emplace_back(res[i]);
      continue;
    }
    // combine them into res[i+1], do not copy res[i] over to combined
    Trace("cad::lazard") << "Combine " << res[i] << " and " << res[i + 1]
                         << std::endl;
    Assert(poly::get_lower(res[i]) <= poly::get_lower(res[i + 1]));
    res[i + 1].set_lower(poly::get_lower(res[i]), poly::get_lower_open(res[i]));
  }

  // always use the last one, it is never dropped
  combined.emplace_back(res.back());
  Trace("cad::lazard") << "To:" << std::endl;
  for (const auto& i : combined)
  {
    Trace("cad::lazard") << "-> " << i << std::endl;
  }
  return combined;
}

}  // namespace cvc5::theory::arith::nl::cad

#else

namespace cvc5::theory::arith::nl::cad {

/**
 * Do a very simple wrapper around the regular poly::infeasible_regions.
 * Warn the user about doing this.
 * This allows for a graceful fallback (albeit with a warning) if CoCoA is not
 * available.
 */
struct LazardEvaluationState
{
  poly::Assignment d_assignment;
};
LazardEvaluation::LazardEvaluation()
    : d_state(std::make_unique<LazardEvaluationState>())
{
}
LazardEvaluation::~LazardEvaluation() {}

void LazardEvaluation::add(const poly::Variable& var, const poly::Value& val)
{
  d_state->d_assignment.set(var, val);
}

void LazardEvaluation::addFreeVariable(const poly::Variable& var) {}

std::vector<poly::Polynomial> LazardEvaluation::reducePolynomial(
    const poly::Polynomial& p) const
{
  return {p};
}
std::vector<poly::Interval> LazardEvaluation::infeasibleRegions(
    const poly::Polynomial& q, poly::SignCondition sc) const
{
  WarningOnce()
      << "CAD::LazardEvaluation is disabled because CoCoA is not available. "
         "Falling back to regular calculation of infeasible regions."
      << std::endl;
  return poly::infeasible_regions(q, d_state->d_assignment, sc);
}

}  // namespace cvc5::theory::arith::nl::cad

#endif
#endif
