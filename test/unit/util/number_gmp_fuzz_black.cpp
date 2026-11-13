/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Randomized differential testing of the GMP implementation of Integer and
 * Rational against GMP, covering both the inline representation of small
 * values and the GMP representation, and values near the int64_t boundaries.
 */

#include <gmpxx.h>

#include <cstdint>
#include <limits>
#include <random>
#include <vector>

#include "test.h"
#include "util/gmp_util.h"
#include "util/integer.h"
#include "util/rational.h"

namespace cvc5::internal {
namespace test {

class TestUtilBlackNumberGmpFuzz : public TestInternal
{
 protected:
  std::mt19937_64 d_rng{12345};

  /** A random integer, biased towards the int64_t boundaries. */
  mpz_class rndZ()
  {
    const int64_t mn = std::numeric_limits<int64_t>::min();
    const int64_t mx = std::numeric_limits<int64_t>::max();
    int64_t k = static_cast<int64_t>(d_rng() % 5) - 2;
    mpz_class z;
    switch (d_rng() % 9)
    {
      case 0: z = static_cast<long>(d_rng() % 201) - 100; break;
      case 1:
        z = static_cast<long>(mn + static_cast<int64_t>(d_rng() % 3));
        break;
      case 2:
        z = static_cast<long>(mx - static_cast<int64_t>(d_rng() % 3));
        break;
      case 3:
        z = mpz_class(1) << (31 + d_rng() % 3);
        z += static_cast<long>(k);
        break;
      case 4:
        z = mpz_class(1) << (62 + d_rng() % 3);
        z += static_cast<long>(k);
        break;
      case 5: z = static_cast<long>(d_rng()); break;
      case 6:
        z = mpz_class(static_cast<unsigned long>(d_rng())) << (d_rng() % 70);
        break;
      case 7: z = static_cast<long>(static_cast<int32_t>(d_rng())); break;
      default: z = static_cast<long>(d_rng() % 7) - 3; break;
    }
    if (d_rng() % 2) z = -z;
    return z;
  }

  /** An Integer for z, sometimes in the promoted (GMP) form. */
  Integer mkI(const mpz_class& z)
  {
    Integer i(z);
    if (d_rng() % 4 == 0) (void)i.getValue();
    return i;
  }
  Rational mkQ(const mpq_class& q)
  {
    Rational r(q);
    if (d_rng() % 4 == 0) (void)r.getValue();
    return r;
  }
  mpq_class rndQ()
  {
    mpz_class n = rndZ(), d = rndZ();
    if (d == 0) d = 1;
    if (d_rng() % 3 == 0) d = 1;
    mpq_class q(n, d);
    q.canonicalize();
    return q;
  }

  static void eqI(const Integer& i, const mpz_class& z)
  {
    ASSERT_TRUE(i.getValue() == z) << i.toString() << " != " << z.get_str();
  }
};

TEST_F(TestUtilBlackNumberGmpFuzz, integer)
{
  for (int it = 0; it < 100000; ++it)
  {
    mpz_class a = rndZ(), b = rndZ();
    Integer x = mkI(a), y = mkI(b);
    eqI(x + y, a + b);
    eqI(x - y, a - b);
    eqI(x * y, a * b);
    eqI(-x, -a);
    eqI(x.abs(), abs(a));
    Integer s = x;
    s += y;
    eqI(s, a + b);
    s = x;
    s -= y;
    eqI(s, a - b);
    s = x;
    s *= y;
    eqI(s, a * b);
    ASSERT_EQ(x == y, a == b);
    ASSERT_EQ(x < y, a < b);
    ASSERT_EQ(x <= y, a <= b);
    ASSERT_EQ(x > y, a > b);
    ASSERT_EQ(x.sgn(), sgn(a));
    ASSERT_EQ(x.hash(), gmpz_hash(a.get_mpz_t()));
    ASSERT_EQ(x.toString(), a.get_str());
    ASSERT_EQ(x.toString(16), a.get_str(16));
    ASSERT_EQ(x.length(), a == 0 ? 1 : mpz_sizeinbase(a.get_mpz_t(), 2));
    ASSERT_EQ(x.fitsSignedInt(), a.fits_sint_p());
    ASSERT_EQ(x.fitsUnsignedInt(), a.fits_uint_p());
    eqI(x.bitwiseAnd(y), a & b);
    eqI(x.bitwiseOr(y), a | b);
    eqI(x.bitwiseXor(y), a ^ b);
    eqI(x.bitwiseNot(), ~a);
    mpz_class g;
    mpz_gcd(g.get_mpz_t(), a.get_mpz_t(), b.get_mpz_t());
    eqI(x.gcd(y), g);
    mpz_class l;
    mpz_lcm(l.get_mpz_t(), a.get_mpz_t(), b.get_mpz_t());
    eqI(x.lcm(y), l);
    ASSERT_EQ(x.divides(y), mpz_divisible_p(b.get_mpz_t(), a.get_mpz_t()) != 0);
    if (b != 0)
    {
      mpz_class q, r;
      mpz_fdiv_qr(q.get_mpz_t(), r.get_mpz_t(), a.get_mpz_t(), b.get_mpz_t());
      eqI(x.floorDivideQuotient(y), q);
      eqI(x.floorDivideRemainder(y), r);
      Integer qq, rr;
      Integer::floorQR(qq, rr, x, y);
      eqI(qq, q);
      eqI(rr, r);
      mpz_cdiv_qr(q.get_mpz_t(), r.get_mpz_t(), a.get_mpz_t(), b.get_mpz_t());
      eqI(x.ceilingDivideQuotient(y), q);
      eqI(x.ceilingDivideRemainder(y), r);
      mpz_class p = a * b;
      eqI(mkI(p).exactQuotient(y), a);
    }
    unsigned bit = d_rng() % 70;
    ASSERT_EQ(x.testBit(bit), mpz_tstbit(a.get_mpz_t(), bit) != 0);
    mpz_class m;
    mpz_fdiv_r_2exp(m.get_mpz_t(), a.get_mpz_t(), bit);
    eqI(x.modByPow2(bit), m);
    mpz_fdiv_q_2exp(m.get_mpz_t(), a.get_mpz_t(), bit);
    eqI(x.divByPow2(bit), m);
    eqI(x.multiplyByPow2(bit), a << bit);
    Integer sb = x;
    sb.setBit(bit, d_rng() % 2);
    mpz_class sa = a;
    if (mpz_tstbit(sb.getValue().get_mpz_t(), bit))
      mpz_setbit(sa.get_mpz_t(), bit);
    else
      mpz_clrbit(sa.get_mpz_t(), bit);
    eqI(sb, sa);
    // equal values have equal hashes, independently of the form
    Integer x2 = mkI(a);
    ASSERT_EQ(x2 == x, true);
    ASSERT_EQ(x2.hash(), x.hash());
  }
}

TEST_F(TestUtilBlackNumberGmpFuzz, rational)
{
  for (int it = 0; it < 100000; ++it)
  {
    mpq_class a = rndQ(), b = rndQ();
    Rational x = mkQ(a), y = mkQ(b);
    ASSERT_TRUE((x + y).getValue() == a + b);
    ASSERT_TRUE((x - y).getValue() == a - b);
    ASSERT_TRUE((x * y).getValue() == a * b);
    ASSERT_TRUE((-x).getValue() == -a);
    ASSERT_TRUE(x.abs().getValue() == abs(a));
    if (b != 0)
    {
      ASSERT_TRUE((x / y).getValue() == a / b);
    }
    Rational s = x;
    s += y;
    ASSERT_TRUE(s.getValue() == a + b);
    s = x;
    s *= y;
    ASSERT_TRUE(s.getValue() == a * b);
    ASSERT_EQ((x.cmp(y) > 0) - (x.cmp(y) < 0),
              (cmp(a, b) > 0) - (cmp(a, b) < 0));
    ASSERT_EQ(x == y, a == b);
    ASSERT_EQ(x < y, a < b);
    ASSERT_EQ(x >= y, a >= b);
    ASSERT_EQ(x.sgn(), sgn(a));
    ASSERT_EQ(x.isIntegral(), a.get_den() == 1);
    ASSERT_EQ(x.toString(), a.get_str());
    ASSERT_TRUE(x.getNumerator().getValue() == a.get_num());
    ASSERT_TRUE(x.getDenominator().getValue() == a.get_den());
    ASSERT_EQ(x.hash(),
              gmpz_hash(a.get_num_mpz_t()) ^ gmpz_hash(a.get_den_mpz_t()));
    mpz_class f;
    mpz_fdiv_q(f.get_mpz_t(), a.get_num_mpz_t(), a.get_den_mpz_t());
    ASSERT_TRUE(x.floor().getValue() == f);
    mpz_cdiv_q(f.get_mpz_t(), a.get_num_mpz_t(), a.get_den_mpz_t());
    ASSERT_TRUE(x.ceiling().getValue() == f);
    ASSERT_EQ(x.getDouble(), a.get_d());
    ASSERT_EQ((x.absCmp(y) > 0) - (x.absCmp(y) < 0),
              (cmp(abs(a), abs(b)) > 0) - (cmp(abs(a), abs(b)) < 0));
    // construction from a GMP integer
    mpz_class z = rndZ();
    ASSERT_TRUE(Rational(z).getValue() == mpq_class(z));
    ASSERT_EQ(Rational(z).hash(), Rational(Integer(z)).hash());
    // construction from numerator and denominator Integers
    mpz_class n = rndZ(), d = rndZ();
    if (d != 0)
    {
      mpq_class q(n, d);
      q.canonicalize();
      ASSERT_TRUE(Rational(mkI(n), mkI(d)).getValue() == q);
    }
    Rational x2 = mkQ(a);
    ASSERT_EQ(x2 == x, true);
    ASSERT_EQ(x2.hash(), x.hash());
  }
}

}  // namespace test
}  // namespace cvc5::internal
