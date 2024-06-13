/******************************************************************************
 * Top contributors (to current version):
 *   Jeff Trull
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2024 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * White box testing of cvc5::internal::expr::attr::AttrHash<>
 */

#include "test_node.h"
#include "expr/attribute.h"
#include <stdint.h>
#include <utility>
#include <array>
#include <cstdint>

namespace cvc5::internal {
namespace test {
// fixtures
class AttrHashFixture : public TestInternal
{
public:
  AttrHashFixture() :
    d_nodeManager{NodeManager::currentNM()},
    d_booleanType{NodeManager::currentNM()->booleanType()} {}

protected:

  template<typename V>
  using Hash = expr::attr::AttrHash<V>;

  NodeManager* d_nodeManager;
  TypeNode d_booleanType;

};

TEST_F(AttrHashFixture, basic)
{
  Node nA = d_nodeManager->mkVar("A", d_booleanType);
  Node nB = d_nodeManager->mkVar("B", d_booleanType);
  Node nC = d_nodeManager->mkVar("C", d_booleanType);
  Node nD = d_nodeManager->mkVar("D", d_booleanType);

  // a constant hash will always be empty (only default constructor)
  const Hash<int> emptyHash;
  EXPECT_EQ(std::distance(emptyHash.begin(), emptyHash.end()), 0u);  // const iterators
  EXPECT_EQ(emptyHash.size(), 0u);

  // add elements using operator[] and varying NodeValue*
  Hash<int> hash1;
  hash1[std::make_pair(0u, nA.d_nv)] = 0;
  hash1[std::make_pair(0u, nB.d_nv)] = 1;
  hash1[std::make_pair(0u, nC.d_nv)] = 2;

  EXPECT_EQ(hash1.size(), 3u);
  EXPECT_EQ(std::distance(hash1.begin(), hash1.end()), 3u); // non-const

  // check const iterators on non-empty hash
  auto const_size_of = [](Hash<int> const & h){ return std::distance(h.begin(), h.end()); };
  EXPECT_EQ(const_size_of(hash1), 3u);

  // make sure the expected values are present
  EXPECT_NE(hash1.find(std::make_pair(0u, nA.d_nv)), hash1.end());
  EXPECT_NE(hash1.find(std::make_pair(0u, nB.d_nv)), hash1.end());
  EXPECT_NE(hash1.find(std::make_pair(0u, nC.d_nv)), hash1.end());

  // add elements using "insert", varying Id
  Hash<int> hash2;
  std::array<typename Hash<int>::iterator::value_type, 3> new_elements{
    std::make_pair(std::make_pair(uint64_t{42}, nA.d_nv), 1),
    std::make_pair(std::make_pair(uint64_t{43}, nA.d_nv), 2),
    std::make_pair(std::make_pair(uint64_t{44}, nA.d_nv), 3)};
  hash2.insert(new_elements.begin(), new_elements.end());
  EXPECT_EQ(hash2.size(), 3u);
  EXPECT_EQ(std::distance(hash2.begin(), hash2.end()), 3u);

  // are they there?
  EXPECT_NE(hash2.find(std::make_pair(uint64_t{42}, nA.d_nv)), hash2.end());
  EXPECT_NE(hash2.find(std::make_pair(uint64_t{43}, nA.d_nv)), hash2.end());
  EXPECT_NE(hash2.find(std::make_pair(uint64_t{44}, nA.d_nv)), hash2.end());

  // erase by iterator
  auto next_after_erase = hash2.erase(hash2.find(std::make_pair(uint64_t{43}, nA.d_nv)));
  // entry is gone
  EXPECT_EQ(hash2.find(std::make_pair(uint64_t{43}, nA.d_nv)), hash2.end());
  // the returned "next" iterator makes sense
  EXPECT_TRUE((next_after_erase == hash2.end()) ||
              ((*next_after_erase) == std::make_pair(std::make_pair(uint64_t{42}, nA.d_nv), 1)) ||
              ((*next_after_erase) == std::make_pair(std::make_pair(uint64_t{44}, nA.d_nv), 3)));

  // erase by NodeValue*
  hash1.eraseBy(nC.d_nv);
  EXPECT_EQ(hash1.find(std::make_pair(0u, nC.d_nv)), hash1.end());
  EXPECT_EQ(hash1.size(), std::size_t{2});
  EXPECT_EQ(std::distance(hash1.begin(), hash1.end()), std::size_t{2});
  EXPECT_NE(hash1.find(std::make_pair(0u, nA.d_nv)), hash1.end());
  EXPECT_NE(hash1.find(std::make_pair(0u, nB.d_nv)), hash1.end());

  // clear
  hash1.clear();
  EXPECT_EQ(hash1.size(), 0ul);

  // swap
  std::swap(hash1, hash2);
  EXPECT_EQ(hash2.size(), 0ul);
  EXPECT_EQ(hash1.size(), 2ul);
  EXPECT_NE(hash1.find(std::make_pair(uint64_t{42}, nA.d_nv)), hash1.end());
  EXPECT_NE(hash1.find(std::make_pair(uint64_t{44}, nA.d_nv)), hash1.end());

}

TEST_F(AttrHashFixture, empty_levels)
{
  // removing the last element from an L2 map
  // (thus causing an empty L2) changes
  // nothing about the operation of the hash overall

  Node nA = d_nodeManager->mkVar("A", d_booleanType);
  Node nB = d_nodeManager->mkVar("B", d_booleanType);
  Node nC = d_nodeManager->mkVar("C", d_booleanType);
  Node nD = d_nodeManager->mkVar("D", d_booleanType);

  std::array<typename Hash<int>::iterator::value_type, 2> new_elements{
    std::make_pair(std::make_pair(uint64_t{42}, nA.d_nv), 1),
    std::make_pair(std::make_pair(uint64_t{43}, nA.d_nv), 2)};

  Hash<int> hash1;
  hash1.insert(new_elements.begin(), new_elements.end());
  EXPECT_EQ(hash1.size(), std::size_t{2});
  auto it = hash1.erase(hash1.begin());
  EXPECT_TRUE((it == hash1.end()) || (it == hash1.begin()));
  EXPECT_EQ(hash1.find((*hash1.begin()).first), hash1.begin());
  EXPECT_EQ(hash1.size(), std::size_t{1});

  // delete the last element
  hash1.erase(hash1.begin());
  EXPECT_EQ(hash1.size(), 0ul);

  // create several L2 maps in a fresh hash
  std::array<typename Hash<int>::iterator::value_type, 8> new_elements2{
    std::make_pair(std::make_pair(uint64_t{11}, nD.d_nv), 3),
    std::make_pair(std::make_pair(uint64_t{12}, nA.d_nv), 3),
    std::make_pair(std::make_pair(uint64_t{13}, nB.d_nv), 2),
    std::make_pair(std::make_pair(uint64_t{14}, nA.d_nv), 4),
    std::make_pair(std::make_pair(uint64_t{15}, nB.d_nv), 2),
    std::make_pair(std::make_pair(uint64_t{16}, nC.d_nv), 5),
    std::make_pair(std::make_pair(uint64_t{17}, nD.d_nv), 6),
    std::make_pair(std::make_pair(uint64_t{18}, nC.d_nv), 7)};

  Hash<int> hash2;
  hash2.insert(new_elements2.begin(), new_elements2.end());
  EXPECT_EQ(hash2.size(), std::size_t{8});

  // remove the two node B attributes one at a time
  hash2.erase(hash2.find(std::make_pair(uint64_t{13}, nB.d_nv)));
  EXPECT_EQ(hash2.find(std::make_pair(uint64_t{13}, nB.d_nv)), hash2.end());
  EXPECT_NE(hash2.find(std::make_pair(uint64_t{15}, nB.d_nv)), hash2.end());
  EXPECT_EQ(hash2[std::make_pair(uint64_t{15}, nB.d_nv)], 2);
  EXPECT_EQ(hash2.size(), std::size_t{7});
  EXPECT_EQ(std::distance(hash2.begin(), hash2.end()), std::size_t{7});

  hash2.erase(hash2.find(std::make_pair(uint64_t{15}, nB.d_nv)));
  EXPECT_EQ(hash2.find(std::make_pair(uint64_t{15}, nB.d_nv)), hash2.end());

  // validate remaining entries
  EXPECT_EQ(hash2.size(), std::size_t{6});
  EXPECT_EQ(std::distance(hash2.begin(), hash2.end()), std::size_t{6});
  EXPECT_NE(hash2.find(std::make_pair(uint64_t{11}, nD.d_nv)), hash2.end());
  EXPECT_NE(hash2.find(std::make_pair(uint64_t{12}, nA.d_nv)), hash2.end());
  EXPECT_NE(hash2.find(std::make_pair(uint64_t{14}, nA.d_nv)), hash2.end());
  EXPECT_NE(hash2.find(std::make_pair(uint64_t{16}, nC.d_nv)), hash2.end());
  EXPECT_NE(hash2.find(std::make_pair(uint64_t{17}, nD.d_nv)), hash2.end());
  EXPECT_NE(hash2.find(std::make_pair(uint64_t{18}, nC.d_nv)), hash2.end());
  EXPECT_EQ(hash2[std::make_pair(uint64_t{11}, nD.d_nv)], 3);
  EXPECT_EQ(hash2[std::make_pair(uint64_t{12}, nA.d_nv)], 3);
  EXPECT_EQ(hash2[std::make_pair(uint64_t{14}, nA.d_nv)], 4);
  EXPECT_EQ(hash2[std::make_pair(uint64_t{16}, nC.d_nv)], 5);
  EXPECT_EQ(hash2[std::make_pair(uint64_t{17}, nD.d_nv)], 6);
  EXPECT_EQ(hash2[std::make_pair(uint64_t{18}, nC.d_nv)], 7);

  // now delete one full NodeValue*'s worth (one L2 map) and reverify
  hash2.eraseBy(nA.d_nv);
  EXPECT_EQ(hash2.size(), std::size_t{4});
  EXPECT_EQ(std::distance(hash2.begin(), hash2.end()), std::size_t{4});
  EXPECT_NE(hash2.find(std::make_pair(uint64_t{11}, nD.d_nv)), hash2.end());
  EXPECT_NE(hash2.find(std::make_pair(uint64_t{16}, nC.d_nv)), hash2.end());
  EXPECT_NE(hash2.find(std::make_pair(uint64_t{17}, nD.d_nv)), hash2.end());
  EXPECT_NE(hash2.find(std::make_pair(uint64_t{18}, nC.d_nv)), hash2.end());
  EXPECT_EQ(hash2[std::make_pair(uint64_t{11}, nD.d_nv)], 3);
  EXPECT_EQ(hash2[std::make_pair(uint64_t{16}, nC.d_nv)], 5);
  EXPECT_EQ(hash2[std::make_pair(uint64_t{17}, nD.d_nv)], 6);
  EXPECT_EQ(hash2[std::make_pair(uint64_t{18}, nC.d_nv)], 7);

}

TEST_F(AttrHashFixture, repeated_inserts)
{
  // when we insert with an existing key, the value is not updated,
  // but it is when we use operator[]

  Node nA = d_nodeManager->mkVar("A", d_booleanType);
  Node nB = d_nodeManager->mkVar("B", d_booleanType);
  Node nC = d_nodeManager->mkVar("C", d_booleanType);

  std::array<typename Hash<int>::iterator::value_type, 5> initial_elements{
    std::make_pair(std::make_pair(uint64_t{42}, nA.d_nv), 2),
    std::make_pair(std::make_pair(uint64_t{43}, nA.d_nv), 1),
    std::make_pair(std::make_pair(uint64_t{42}, nB.d_nv), 4),
    std::make_pair(std::make_pair(uint64_t{43}, nB.d_nv), 5),
    std::make_pair(std::make_pair(uint64_t{42}, nC.d_nv), 2)};

  Hash<int> hash;
  hash.insert(initial_elements.begin(), initial_elements.end());

  // attempt to change two entries using insert
  std::array<typename Hash<int>::iterator::value_type, 2> new_elements{
    std::make_pair(std::make_pair(uint64_t{42}, nA.d_nv), 6),
    std::make_pair(std::make_pair(uint64_t{42}, nC.d_nv), 8)};
  hash.insert(new_elements.begin(), new_elements.end());

  // entries should be unchanged (insert doesn't alter existing entries)
  EXPECT_EQ(hash.size(), std::size_t{5});
  EXPECT_EQ(hash[std::make_pair(uint64_t{42}, nA.d_nv)], 2);
  EXPECT_EQ(hash[std::make_pair(uint64_t{42}, nC.d_nv)], 2);
  EXPECT_EQ(*hash.find(std::make_pair(uint64_t{42}, nA.d_nv)),
            std::make_pair(std::make_pair(uint64_t{42}, nA.d_nv), 2));
  EXPECT_EQ(*hash.find(std::make_pair(uint64_t{42}, nC.d_nv)),
            std::make_pair(std::make_pair(uint64_t{42}, nC.d_nv), 2));

  // change two entries using operator[]
  hash[std::make_pair(uint64_t{42}, nB.d_nv)] = 10;
  hash[std::make_pair(uint64_t{42}, nC.d_nv)] = 12;

  // entries should be changed this time
  EXPECT_EQ(hash[std::make_pair(uint64_t{42}, nB.d_nv)], 10);
  EXPECT_EQ(hash[std::make_pair(uint64_t{42}, nC.d_nv)], 12);
  EXPECT_EQ(*hash.find(std::make_pair(uint64_t{42}, nB.d_nv)),
            std::make_pair(std::make_pair(uint64_t{42}, nB.d_nv), 10));
  EXPECT_EQ(*hash.find(std::make_pair(uint64_t{42}, nC.d_nv)),
            std::make_pair(std::make_pair(uint64_t{42}, nC.d_nv), 12));
}

} // namespace test
} // namespace cvc5::internal
