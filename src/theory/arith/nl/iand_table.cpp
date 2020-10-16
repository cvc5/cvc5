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

// computes (bv_to_int ((_ extract i+size-1 i) (int_to_bv x))))
Node intExtract(Node x, uint64_t i, uint64_t size)
{
  Assert(size > 0);
  NodeManager* nm = NodeManager::currentNM();
  // extract definition in integers is:
  // (mod (div a (two_to_the j)) (two_to_the (+ (- i j) 1))))
  Node extract =
      nm->mkNode(kind::INTS_MODULUS_TOTAL,
                 nm->mkNode(kind::INTS_DIVISION_TOTAL, x, pow2(i * size)),
                 pow2(size));
  return extract;
}

Node IAndTable::createITEFromTable(
    Node x,
    Node y,
    uint64_t granularity,
    const std::map<std::pair<int64_t, int64_t>, uint64_t>& table)
{
  NodeManager* nm = NodeManager::currentNM();
  Assert(granularity <= 8);
  uint64_t num_of_values = ((uint64_t)pow(2, granularity));
  // The table represents a function from pairs of integers to integers, where
  // all integers are between 0 (inclusive) and num_of_values (exclusive).
  // additionally, there is a default value (-1, -1).
  Assert(table.size() == 1 + ((uint64_t)(num_of_values * num_of_values)));
  // start with the default, most common value.
  // this value is represented in the table by (-1, -1).
  Node ite = nm->mkConst<Rational>(table.at(std::make_pair(-1, -1)));
  for (uint64_t i = 0; i < num_of_values; i++)
  {
    for (uint64_t j = 0; j < num_of_values; j++)
    {
      // skip the most common value, as it was already stored.
      if (table.at(std::make_pair(i, j)) == table.at(std::make_pair(-1, -1)))
      {
        continue;
      }
      // append the current value to the ite.
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
  Assert(0 < granularity && granularity <= 8);
  // Standardize granularity.
  // If it is greater than bvsize, it is set to bvsize.
  // Otherwise, it is set to the closest (going down)  divider of bvsize.
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

  // Create the sum.
  // For granularity 1, the sum has bvsize elements.
  // In contrast, if bvsize = granularity, sum has one element.
  // Each element in the sum is an ite that corresponds to the generated table,
  // multiplied by the appropriate power of two.
  // More details are in bv_to_int.h .

  // number of elements in the sum expression
  uint64_t sumSize = bvsize / granularity;
  // initialize the sum
  Node sumNode = nm->mkConst<Rational>(0);
  // compute the table for the current granularity if needed
  if (d_bvandTable.find(granularity) == d_bvandTable.end())
  {
    computeAndTable(granularity);
  }
  const std::map<std::pair<int64_t, int64_t>, uint64_t>& table =
      d_bvandTable[granularity];
  for (uint64_t i = 0; i < sumSize; i++)
  {
    // compute the current blocks of x and y
    Node xExtract = intExtract(x, i, granularity);
    Node yExtract = intExtract(y, i, granularity);
    // compute the ite for this part
    Node sumPart = createITEFromTable(xExtract, yExtract, granularity, table);
    // append the current block to the sum
    sumNode =
        nm->mkNode(kind::PLUS,
                   sumNode,
                   nm->mkNode(kind::MULT, pow2(i * granularity), sumPart));
  }
  return sumNode;
}

void IAndTable::computeAndTable(uint64_t granularity)
{
  Assert(d_bvandTable.find(granularity) == d_bvandTable.end());
  // the table was not yet computed
  std::map<std::pair<int64_t, int64_t>, uint64_t> table;
  uint64_t num_of_values = ((uint64_t)pow(2, granularity));
  // populate the table with all the values
  for (uint64_t i = 0; i < num_of_values; i++)
  {
    for (uint64_t j = 0; j < num_of_values; j++)
    {
      // compute
      // (bv_to_int (bvand ((int_to_bv granularity) i) ((int_to_bv granularity)
      // j)))
      int64_t sum = 0;
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
  // optimize the table by identifying and adding the default value
  addDefaultValue(table, num_of_values);
  Assert(table.size() == 1 + (static_cast<uint64_t>(num_of_values * num_of_values)));
  // store the table in the cache and return it
  d_bvandTable[granularity] = table;
}

void IAndTable::addDefaultValue(
    std::map<std::pair<int64_t, int64_t>, uint64_t>& table,
    uint64_t num_of_values)
{
  // map each result to the number of times it occurs
  std::map<uint64_t, uint64_t> counters;
  for (uint64_t i = 0; i <= num_of_values; i++)
  {
    counters[i] = 0;
  }
  for (const std::pair<std::pair<int64_t, int64_t>, uint64_t>& element : table)
  {
    uint64_t result = element.second;
    counters[result]++;
  }

  // compute the most common result
  uint64_t most_common_result = 0;
  uint64_t max_num_of_occ = 0;
  for (uint64_t i = 0; i <= num_of_values; i++)
  {
    if (counters[i] >= max_num_of_occ)
    {
      max_num_of_occ = counters[i];
      most_common_result = i;
    }
  }
  // sanity check: some value appears at least once.
  Assert(max_num_of_occ != 0);

  // -1 is the default case of the table.
  // add it to the table
  table[std::make_pair(-1, -1)] = most_common_result;
}

}  // namespace nl
}  // namespace arith
}  // namespace theory
}  // namespace CVC4
