/*********************                                                        */
/*! \file nl_iand_utils.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Yoni Zohar
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Implementation of utilities for the non-linear solver
 **/

#include "cvc4_private.h"
#include "theory/arith/nl/nl_iand_utils.h"
#include "theory/arith/nl/nl_model.h"
#include <cmath>
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




Node IAndHelper::createITEFromTable(
    Node x,
    Node y,
    uint64_t granularity,
    std::map<std::pair<int64_t, int64_t>, int64_t> table)
{
  Assert(granularity <= 8);
  int64_t num_of_values = ((int64_t)pow(2, granularity)) ;
  // The table represents a function from pairs of integers to integers, where
  // all integers are between 0 (inclusive) and num_of_values (exclusive).
  Assert(table.size() == 1+ ((uint64_t)(num_of_values * num_of_values)));
  //start with the default, most common value
  NodeManager* nm = NodeManager::currentNM();
  Node ite = nm->mkConst<Rational>(table[std::make_pair(-1, -1)]);
  for (int64_t i = 0; i < num_of_values; i++)
  {
    for (int64_t j = 0; j < num_of_values; j++)
    {
      if (table[std::make_pair(i,j)] == table[std::make_pair(-1,-1)])
      {
        continue;
      }
      ite = nm->mkNode(
          kind::ITE,
          nm->mkNode(
              kind::AND,
              nm->mkNode(kind::EQUAL, x, nm->mkConst<Rational>(i)),
              nm->mkNode(kind::EQUAL, y, nm->mkConst<Rational>(j))),
          nm->mkConst<Rational>(table[std::make_pair(i, j)]),
          ite);
    }
  }
  return ite;
}

Node IAndHelper::createBitwiseNode(Node x,
                                Node y,
                                uint64_t bvsize,
				   uint64_t granularity)
{
  /**
   * Standardize granularity.
   * If it is greater than bvsize, it is set to bvsize.
   * Otherwise, it is set to the closest (going down)  divider of bvsize.
   */
  Assert(granularity > 0);
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

  /*
   * Create the sum.
   * For granularity 1, the sum has bvsize elements.
   * In contrast, if bvsize = granularity, sum has one element.
   * Each element in the sum is an ite that corresponds to the generated table,
   * multiplied by the appropriate power of two.
   * More details are in bv_to_int.h .
   */
  uint64_t sumSize = bvsize / granularity;
  NodeManager* nm = NodeManager::currentNM();
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
    Node sumPart = createPart(xExtract, yExtract, granularity);
    sumNode = nm->mkNode(kind::PLUS,
                         sumNode,
                         nm->mkNode(kind::MULT, pow2(i * granularity), sumPart));
  }
  return sumNode;
}

Node IAndHelper::createPart(Node x, Node y, uint64_t granularity) {
    std::map<std::pair<int64_t, int64_t>, int64_t> table = getAndTable(granularity);
    Node ite = createITEFromTable(x, y, granularity, table);
    return ite;
  }

std::map<std::pair<int64_t, int64_t>, int64_t> IAndHelper::getAndTable(uint64_t granularity) {
  if (d_bvandTable.find(granularity) != d_bvandTable.end()) {
    return d_bvandTable[granularity];
  }
  //the table was not yet computed
  std::map<std::pair<int64_t, int64_t>, int64_t> table;
  int64_t num_of_values = ((int64_t)pow(2, granularity));
  bool (*fp)(bool, bool);
  fp = oneBitAnd;
  for (int64_t i = 0; i < num_of_values; i++)
  {
    for (int64_t j = 0; j < num_of_values; j++)
    {
      int64_t sum = 0;
      for (uint64_t n = 0; n < granularity; n++)
      {
        // b is the result of f on the current bit
        bool b = (*fp)((((i >> n) & 1) == 1), (((j >> n) & 1) == 1));
        // add the corresponding power of 2 only if the result is 1
        if (b)
        {
          sum += 1 << n;
        }
      }
      table[std::make_pair(i, j)] = sum;
    }
  }
   addDefaultValue(table, num_of_values);
   Assert(table.size() == 1+ ((uint64_t)(num_of_values * num_of_values)));
   d_bvandTable[granularity] = table;
   return table;
}

void IAndHelper::addDefaultValue(std::map<std::pair<int64_t, int64_t>, int64_t>& table, int64_t num_of_values) {
  std::map<int64_t, int64_t> counters;
  for (int64_t i = 0; i <= num_of_values;i++) {

    counters[i] = 0;
  }
  for (std::pair<std::pair<int64_t, int64_t>, int64_t> element : table) {
    int64_t result = element.second;
    counters[result]++;
  }
  int64_t most_common_result = -1;
  int64_t max_num_of_occ = -1;
  for (int64_t i=0; i <= num_of_values; i++) {
    if (counters[i] > max_num_of_occ) {
      max_num_of_occ = counters[i];
      most_common_result = i;
    }
  }
  //-1 is the default case of the table
  table[std::make_pair(-1,-1)] = most_common_result;
}


  
}  // namespace nl
}  // namespace arith
}  // namespace theory
}  // namespace CVC4
