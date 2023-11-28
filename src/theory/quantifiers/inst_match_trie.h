/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Morgan Deters, Aina Niemetz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Inst match trie class.
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__QUANTIFIERS__INST_MATCH_TRIE_H
#define CVC5__THEORY__QUANTIFIERS__INST_MATCH_TRIE_H

#include <map>

#include "context/cdlist.h"
#include "context/cdo.h"
#include "expr/node.h"
#include "smt/env_obj.h"

namespace cvc5::internal {
namespace theory {
namespace quantifiers {

class QuantifiersState;

/** trie for InstMatch objects
 *
 * This class is used for storing instantiations of a quantified formula q.
 * It is a trie data structure for which entries can be added and removed.
 * This class has interfaces for adding instantiations that are either
 * represented by std::vectors or InstMatch objects (see inst_match.h).
 */
class InstMatchTrie
{
 public:
  /** index ordering */
  class ImtIndexOrder
  {
   public:
    std::vector<unsigned> d_order;
  };

 public:
  InstMatchTrie() {}
  ~InstMatchTrie() {}
  /** exists inst match
   *
   * This method considers the entry given by m, starting at the given index.
   * The domain of m is the bound variables of quantified formula q.
   * It returns true if (the suffix) of m exists in this trie.
   */
  bool existsInstMatch(Node q,
                       const std::vector<Node>& m,
                       ImtIndexOrder* imtio = nullptr,
                       unsigned index = 0);
  /** add inst match
   *
   * This method adds (the suffix of) m starting at the given index to this
   * trie, and returns true if and only if m did not already occur in this trie.
   * The domain of m is the bound variables of quantified formula q.
   */
  bool addInstMatch(Node f,
                    const std::vector<Node>& m,
                    ImtIndexOrder* imtio = nullptr,
                    bool onlyExist = false,
                    unsigned index = 0);
  /**
   * Adds the instantiations for q into insts.
   */
  void getInstantiations(Node q, std::vector<std::vector<Node>>& insts) const;

  /** clear the data of this class */
  void clear();
  /** print this class */
  void print(std::ostream& out, Node q) const;
  /** the data */
  std::map<Node, InstMatchTrie> d_data;

 private:
  /** Helper for getInstantiations.*/
  void getInstantiations(Node q,
                         std::vector<std::vector<Node>>& insts,
                         std::vector<Node>& terms) const;
  /** helper for print
   * terms accumulates the path we are on in the trie.
   */
  void print(std::ostream& out, Node q, std::vector<TNode>& terms) const;
};

/** trie for InstMatch objects
 *
 * This is a context-dependent version of the above class.
 */
class CDInstMatchTrie
{
 public:
  CDInstMatchTrie(context::Context* c) : d_valid(c, false) {}
  ~CDInstMatchTrie();

  /** exists inst match
   *
   * This method considers the entry given by m, starting at the given index.
   * The domain of m is the bound variables of quantified formula q.
   * It returns true if (the suffix) of m exists in this trie.
   * It additionally takes a context c, for which the entry is valid in.
   */
  bool existsInstMatch(context::Context* context,
                       Node q,
                       const std::vector<Node>& m,
                       unsigned index = 0);
  /** add inst match
   *
   * This method adds (the suffix of) m starting at the given index to this
   * trie, and returns true if and only if m did not already occur in this trie.
   * The domain of m is the bound variables of quantified formula q.
   * It additionally takes a context c, for which the entry is valid in.
   */
  bool addInstMatch(context::Context* context,
                    Node q,
                    const std::vector<Node>& m,
                    unsigned index = 0,
                    bool onlyExist = false);
  /**
   * Adds the instantiations for q into insts.
   */
  void getInstantiations(Node q, std::vector<std::vector<Node>>& insts) const;

  /** print this class */
  void print(std::ostream& out, Node q) const;

 private:
  /** Helper for getInstantiations.*/
  void getInstantiations(Node q,
                         std::vector<std::vector<Node>>& insts,
                         std::vector<Node>& terms) const;
  /** helper for print
   * terms accumulates the path we are on in the trie.
   */
  void print(std::ostream& out, Node q, std::vector<TNode>& terms) const;
  /** the data */
  std::map<Node, CDInstMatchTrie*> d_data;
  /** is valid */
  context::CDO<bool> d_valid;
};

/** inst match trie ordered
 *
 * This is an ordered version of the context-independent instantiation match
 * trie. It stores a variable order and a base InstMatchTrie.
 */
class InstMatchTrieOrdered
{
 public:
  InstMatchTrieOrdered(InstMatchTrie::ImtIndexOrder* imtio) : d_imtio(imtio) {}
  ~InstMatchTrieOrdered() {}
  /** get the ordering */
  InstMatchTrie::ImtIndexOrder* getOrdering() { return d_imtio; }
  /** get the trie data */
  InstMatchTrie* getTrie() { return &d_imt; }
  /** add match m for quantified formula q
   *
   * This method returns true if the match m was not previously added to this
   * class.
   */
  bool addInstMatch(Node q, const std::vector<Node>& m);
  /** returns true if this trie contains m
   *
   * This method returns true if the match m exists in this
   * class.
   */
  bool existsInstMatch(Node q, const std::vector<Node>& m);

 private:
  /** the ordering */
  InstMatchTrie::ImtIndexOrder* d_imtio;
  /** the data of this class */
  InstMatchTrie d_imt;
};

}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5__THEORY__QUANTIFIERS__INST_MATCH_TRIE_H */
