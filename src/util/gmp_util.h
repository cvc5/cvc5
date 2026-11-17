/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * GMP utilities.
 */

#include "cvc5_public.h"

#ifndef CVC5__GMP_UTIL_H
#define CVC5__GMP_UTIL_H

#include <gmpxx.h>

#include <cstddef>
#include <cstdint>
#include <limits>

// the following includes are only required if CVC5_NEED_INT64_T_OVERLOADS is
// defined.
#ifdef CVC5_NEED_INT64_T_OVERLOADS
#include <string>
#include <type_traits>
#endif /* CVC5_NEED_INT64_T_OVERLOADS */

namespace cvc5::internal {

/** Hashes the gmp integer primitive in a word by word fashion. */
inline size_t gmpz_hash(const mpz_t toHash)
{
  size_t hash = 0;
  for (int i = 0, n = mpz_size(toHash); i < n; ++i)
  {
    mp_limb_t limb = mpz_getlimbn(toHash, i);
    hash = hash * 2;
    hash = hash ^ limb;
  }
  return hash;
} /* gmpz_hash() */

/*
 * Conversions between 64-bit integers and GMP integers that do not depend on
 * the size of long (32 bits on Windows) or of GMP limbs (32 bits on 32-bit
 * platforms, e.g., WebAssembly).
 */

static_assert(GMP_NUMB_BITS == 64 || GMP_NUMB_BITS == 32,
              "GMP limbs must have 64 or 32 bits and no nails");

/** The number of GMP limbs needed for a 64-bit magnitude. */
constexpr int gmpz_limbs_per_u64 = 64 / GMP_NUMB_BITS;

/**
 * Stores the 64-bit magnitude x into gmpz_limbs_per_u64 limbs, least
 * significant first, as GMP stores it.
 */
inline void gmpz_limbs_from_u64(mp_limb_t* limbs, uint64_t x)
{
  for (int i = 0; i < gmpz_limbs_per_u64; ++i)
  {
    limbs[i] = static_cast<mp_limb_t>(x >> (i * GMP_NUMB_BITS));
  }
}

/** The value of gmpz_hash() for an integer whose absolute value is x. */
inline size_t gmpz_hash_u64(uint64_t x)
{
  mp_limb_t limbs[gmpz_limbs_per_u64];
  gmpz_limbs_from_u64(limbs, x);
  int n = gmpz_limbs_per_u64;
  while (n > 0 && limbs[n - 1] == 0)
  {
    --n;
  }
  size_t hash = 0;
  for (int i = 0; i < n; ++i)
  {
    hash = hash * 2;
    hash = hash ^ limbs[i];
  }
  return hash;
}

/** Sets z to the value of x. */
inline void gmpz_set_int64(mpz_ptr z, int64_t x)
{
  if constexpr (sizeof(long) == sizeof(int64_t))
  {
    mpz_set_si(z, static_cast<long>(x));
  }
  else
  {
    uint64_t a =
        x < 0 ? 0 - static_cast<uint64_t>(x) : static_cast<uint64_t>(x);
    mpz_import(z, 1, -1, sizeof(uint64_t), 0, 0, &a);
    if (x < 0)
    {
      mpz_neg(z, z);
    }
  }
}

/** Sets z to the value of x. */
inline void gmpz_set_uint64(mpz_ptr z, uint64_t x)
{
  if constexpr (sizeof(unsigned long) == sizeof(uint64_t))
  {
    mpz_set_ui(z, static_cast<unsigned long>(x));
  }
  else
  {
    mpz_import(z, 1, -1, sizeof(uint64_t), 0, 0, &x);
  }
}

/** If z fits into an int64_t, sets x to its value and returns true. */
inline bool gmpz_get_int64(mpz_srcptr z, int64_t* x)
{
  if constexpr (sizeof(long) == sizeof(int64_t))
  {
    if (!mpz_fits_slong_p(z))
    {
      return false;
    }
    *x = mpz_get_si(z);
    return true;
  }
  else
  {
    size_t n = mpz_size(z);
    if (n > static_cast<size_t>(gmpz_limbs_per_u64))
    {
      return false;
    }
    uint64_t a = 0;
    for (size_t i = 0; i < n; ++i)
    {
      a |= static_cast<uint64_t>(mpz_getlimbn(z, i)) << (i * GMP_NUMB_BITS);
    }
    constexpr uint64_t max = std::numeric_limits<int64_t>::max();
    if (mpz_sgn(z) >= 0)
    {
      if (a > max)
      {
        return false;
      }
      *x = static_cast<int64_t>(a);
    }
    else
    {
      if (a > max + 1)
      {
        return false;
      }
      // -a, also for a = 2^63
      *x = -static_cast<int64_t>(a - 1) - 1;
    }
    return true;
  }
}

#ifdef CVC5_NEED_INT64_T_OVERLOADS
/*
 * Before converting an int64_t/uint64_t to a GMP value, we need to check if
 * the input value will fit inside of a (un)signed long, which is the largest
 * overload supported by GMP's C++ API.
 *
 * If the input value is *larger* than (un)signed long, then we use GMP's
 * string-based API to construct the value.
 *
 * The following function looks-up the largest matching type against the input
 * type, checks the range, and then decides to use the string-based overloads
 * if the value does not fit.
 */
template <typename T>
mpz_class construct_mpz(T z)
{
  /* only use this with int64_t or uint64_t */
  static_assert(
      std::is_same<T, int64_t>::value || std::is_same<T, uint64_t>::value,
      "construct_mpz only supports int64_t or uint64_t");

  /* what's the largest GMP-supported type? */
  using gmp_type = typename std::
      conditional<std::is_signed<T>::value, signed long, unsigned long>::type;

  /* result value */
  mpz_class result;

  /* if our input fits inside of the range of the largest GMP-support type, we
   * construct result based on the value */
  if (std::numeric_limits<gmp_type>::min() <= z
      && z <= std::numeric_limits<gmp_type>::max())
  {
    result = static_cast<gmp_type>(z);
  }
  else
  {
    /* otherwise, use the string-based methods */
    result = std::to_string(z);
  }
  return result;
}
#endif /* CVC5_NEED_INT64_T_OVERLOADS */
}  // namespace cvc5::internal

#endif /* CVC5__GMP_UTIL_H */
