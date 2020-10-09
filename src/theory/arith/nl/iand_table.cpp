/*********************                                                        */
/*! \file iand_table.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Yoni Zohar
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Utilities to maintain finite tables that represent
 ** the value of iand.
 **/

#include "theory/arith/nl/iand_table.h"

#include <cmath>

#include "cvc4_private.h"
#include "theory/arith/nl/nl_model.h"
namespace CVC4 {
namespace theory {
namespace arith {
namespace nl {

static Rational intpow2(uint64_t b)
{
  return Rational(Integer(2).pow(b), Integer(1));
}

Node pow2(uint64_t k)
{
  Assert(k >= 0);
  NodeManager* nm = NodeManager::currentNM();
  return nm->mkConst<Rational>(intpow2(k));
}

bool oneBitAnd(bool a, bool b) { return (a && b); }

Node IAndTable::createITEFromTable(
    Node x,
    Node y,
    uint64_t granularity,
    const std::map<std::pair<uint64_t, uint64_t>, uint64_t>& table)
{
  NodeManager* nm = NodeManager::currentNM();
  Assert(granularity <= 8);
  uint64_t max_value = ((uint64_t)pow(2, granularity));
  // The table represents a function from pairs of integers to integers, where
  // all integers are between 0 (inclusive) and max_value (exclusive).
  Assert(table.size() == max_value * max_value);
  Node ite = nm->mkConst<Rational>(table.at(std::make_pair(0, 0)));
  for (uint64_t i = 0; i < max_value; i++)
  {
    for (uint64_t j = 0; j < max_value; j++)
    {
      if ((i == 0) && (j == 0))
      {
        continue;
      }
      ite = nm->mkNode(
          kind::ITE,
          nm->mkNode(kind::AND,
                     nm->mkNode(kind::EQUAL, x, nm->mkConst<Rational>(i)),
                     nm->mkNode(kind::EQUAL, y, nm->mkConst<Rational>(j))),
          nm->mkConst<Rational>(table.at(std::make_pair(i, j))),
          ite);
    }
  }
  return ite;
}

Node IAndTable::createBitwiseNode(Node x,
                                  Node y,
                                  uint64_t bvsize,
                                  uint64_t granularity)
{
  NodeManager* nm = NodeManager::currentNM();
  /**
   * Standardize granularity.
   * If it is greater than bvsize, it is set to bvsize.
   * Otherwise, it is set to the closest (going down)  divider of bvsize.
   */
  Assert(0 < granularity && granularity <= 8);
  if (granularity > bvsize)
  {
    granularity = bvsize;
  }
  else
  {
    while (bvsize % granularity != 0)
    {
      granularity = granularity - 1;
    }
  }
  // transform f into a table
  // f is defined over 1 bit, while the table is defined over `granularity` bits
  std::map<std::pair<uint64_t, uint64_t>, uint64_t> table;
  uint64_t max_value = ((uint64_t)pow(2, granularity));
  for (uint64_t i = 0; i < max_value; i++)
  {
    for (uint64_t j = 0; j < max_value; j++)
    {
      uint64_t sum = 0;
      for (uint64_t n = 0; n < granularity; n++)
      {
        // b is the result of f on the current bit
        bool b = oneBitAnd((((i >> n) & 1) == 1), (((j >> n) & 1) == 1));
        // add the corresponding power of 2 only if the result is 1
        if (b)
        {
          sum += 1 << n;
        }
      }
      table[std::make_pair(i, j)] = sum;
    }
  }
  Assert(table.size() == max_value * max_value);

  /*
   * Create the sum.
   * For granularity 1, the sum has bvsize elements.
   * In contrast, if bvsize = granularity, sum has one element.
   * Each element in the sum is an ite that corresponds to the generated table,
   * multiplied by the appropriate power of two.
   * More details are in bv_to_int.h .
   */
  uint64_t sumSize = bvsize / granularity;
  Node sumNode = nm->mkConst<Rational>(0);
  /**
   * extract definition in integers is:
   * (define-fun intextract ((k Int) (i Int) (j Int) (a Int)) Int
   * (mod (div a (two_to_the j)) (two_to_the (+ (- i j) 1))))
   */
  for (uint64_t i = 0; i < sumSize; i++)
  {
    Node xExtract = nm->mkNode(
        kind::INTS_MODULUS_TOTAL,
        nm->mkNode(kind::INTS_DIVISION_TOTAL, x, pow2(i * granularity)),
        pow2(granularity));
    Node yExtract = nm->mkNode(
        kind::INTS_MODULUS_TOTAL,
        nm->mkNode(kind::INTS_DIVISION_TOTAL, y, pow2(i * granularity)),
        pow2(granularity));
    Node ite = createITEFromTable(xExtract, yExtract, granularity, table);
    sumNode = nm->mkNode(kind::PLUS,
                         sumNode,
                         nm->mkNode(kind::MULT, pow2(i * granularity), ite));
  }
  return sumNode;
}

}  // namespace nl
}  // namespace arith
}  // namespace theory
}  // namespace CVC4
