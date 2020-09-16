/*********************                                                        */
/*! \file inst_match_trie.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Morgan Deters, Mathias Preiner
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief inst match class
 **/

#include "cvc4_private.h"

#ifndef CVC4__THEORY__QUANTIFIERS__INST_MATCH_TRIE_H
#define CVC4__THEORY__QUANTIFIERS__INST_MATCH_TRIE_H

#include <map>

#include "context/cdlist.h"
#include "context/cdo.h"
#include "expr/node.h"
#include "theory/quantifiers/inst_match.h"

namespace CVC4 {
namespace theory {

class QuantifiersEngine;
class EqualityQuery;

namespace inst {

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
   * If modEq is true, we check for duplication modulo equality the current
   * equalities in the active equality engine of qe.
   */
  bool existsInstMatch(QuantifiersEngine* qe,
                       Node q,
                       InstMatch& m,
                       bool modEq = false,
                       ImtIndexOrder* imtio = NULL,
                       unsigned index = 0)
  {
    return !addInstMatch(qe, q, m, modEq, imtio, true, index);
  }
  /** exists inst match, vector version */
  bool existsInstMatch(QuantifiersEngine* qe,
                       Node q,
                       std::vector<Node>& m,
                       bool modEq = false,
                       ImtIndexOrder* imtio = NULL,
                       unsigned index = 0)
  {
    return !addInstMatch(qe, q, m, modEq, imtio, true, index);
  }
  /** add inst match
   *
   * This method adds (the suffix of) m starting at the given index to this
   * trie, and returns true if and only if m did not already occur in this trie.
   * The domain of m is the bound variables of quantified formula q.
   * If modEq is true, we check for duplication modulo equality the current
   * equalities in the active equality engine of qe.
   */
  bool addInstMatch(QuantifiersEngine* qe,
                    Node q,
                    InstMatch& m,
                    bool modEq = false,
                    ImtIndexOrder* imtio = NULL,
                    bool onlyExist = false,
                    unsigned index = 0)
  {
    return addInstMatch(qe, q, m.d_vals, modEq, imtio, onlyExist, index);
  }
  /** add inst match, vector version */
  bool addInstMatch(QuantifiersEngine* qe,
                    Node f,
                    std::vector<Node>& m,
                    bool modEq = false,
                    ImtIndexOrder* imtio = NULL,
                    bool onlyExist = false,
                    unsigned index = 0);
  /** remove inst match
   *
   * This removes (the suffix of) m starting at the given index from this trie.
   * It returns true if and only if this entry existed in this trie.
   * The domain of m is the bound variables of quantified formula q.
   */
  bool removeInstMatch(Node f,
                       std::vector<Node>& m,
                       ImtIndexOrder* imtio = NULL,
                       unsigned index = 0);
  /** record instantiation lemma
   *
   * This records that the instantiation lemma lem corresponds to the entry
   * given by (the suffix of) m starting at the given index.
   */
  bool recordInstLemma(Node q,
                       std::vector<Node>& m,
                       Node lem,
                       ImtIndexOrder* imtio = NULL,
                       unsigned index = 0);

  /** get instantiations
   *
   * This gets the set of instantiation lemmas that were recorded in this trie
   * via calls to recordInstLemma. If useActive is true, we only add
   * instantiations that occur in active.
   */
  void getInstantiations(std::vector<Node>& insts,
                         Node q,
                         QuantifiersEngine* qe,
                         bool useActive,
                         std::vector<Node>& active)
  {
    std::vector<Node> terms;
    getInstantiations(insts, q, terms, qe, useActive, active);
  }
  /** get explanation for inst lemmas
   *
   * This gets the explanation for the instantiation lemmas in lems for
   * quantified formula q, for which this trie stores instantiation matches for.
   * For each instantiation lemma lem recording in this trie via calls to
   * recordInstLemma, we map lem to q in map quant, and lem to its corresponding
   * vector of terms in tvec.
   */
  void getExplanationForInstLemmas(
      Node q,
      const std::vector<Node>& lems,
      std::map<Node, Node>& quant,
      std::map<Node, std::vector<Node> >& tvec) const
  {
    std::vector<Node> terms;
    getExplanationForInstLemmas(q, terms, lems, quant, tvec);
  }

  /** clear the data of this class */
  void clear() { d_data.clear(); }
  /** print this class */
  void print(std::ostream& out,
             Node q,
             bool useActive,
             std::vector<Node>& active) const
  {
    std::vector<TNode> terms;
    print(out, q, terms, useActive, active);
  }
  /** the data */
  std::map<Node, InstMatchTrie> d_data;

 private:
  /** helper for print
   * terms accumulates the path we are on in the trie.
   */
  void print(std::ostream& out,
             Node q,
             std::vector<TNode>& terms,
             bool useActive,
             std::vector<Node>& active) const;
  /** helper for get instantiations
   * terms accumulates the path we are on in the trie.
   */
  void getInstantiations(std::vector<Node>& insts,
                         Node q,
                         std::vector<Node>& terms,
                         QuantifiersEngine* qe,
                         bool useActive,
                         std::vector<Node>& active) const;
  /** helper for get explantaion for inst lemmas
   * terms accumulates the path we are on in the trie.
   */
  void getExplanationForInstLemmas(
      Node q,
      std::vector<Node>& terms,
      const std::vector<Node>& lems,
      std::map<Node, Node>& quant,
      std::map<Node, std::vector<Node> >& tvec) const;
  /** set instantiation lemma at this node in the trie */
  void setInstLemma(Node n)
  {
    d_data.clear();
    d_data[n].clear();
  }
  /** does this node of the trie store an instantiation lemma? */
  bool hasInstLemma() const { return !d_data.empty(); }
  /** get the instantiation lemma stored in this node of the trie */
  Node getInstLemma() const { return d_data.begin()->first; }
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
   * If modEq is true, we check for duplication modulo equality the current
   * equalities in the active equality engine of qe.
   * It additionally takes a context c, for which the entry is valid in.
   */
  bool existsInstMatch(QuantifiersEngine* qe,
                       Node q,
                       InstMatch& m,
                       context::Context* c,
                       bool modEq = false,
                       unsigned index = 0)
  {
    return !addInstMatch(qe, q, m, c, modEq, index, true);
  }
  /** exists inst match, vector version */
  bool existsInstMatch(QuantifiersEngine* qe,
                       Node q,
                       std::vector<Node>& m,
                       context::Context* c,
                       bool modEq = false,
                       unsigned index = 0)
  {
    return !addInstMatch(qe, q, m, c, modEq, index, true);
  }
  /** add inst match
   *
   * This method adds (the suffix of) m starting at the given index to this
   * trie, and returns true if and only if m did not already occur in this trie.
   * The domain of m is the bound variables of quantified formula q.
   * If modEq is true, we check for duplication modulo equality the current
   * equalities in the active equality engine of qe.
   * It additionally takes a context c, for which the entry is valid in.
   */
  bool addInstMatch(QuantifiersEngine* qe,
                    Node q,
                    InstMatch& m,
                    context::Context* c,
                    bool modEq = false,
                    unsigned index = 0,
                    bool onlyExist = false)
  {
    return addInstMatch(qe, q, m.d_vals, c, modEq, index, onlyExist);
  }
  /** add inst match, vector version */
  bool addInstMatch(QuantifiersEngine* qe,
                    Node q,
                    std::vector<Node>& m,
                    context::Context* c,
                    bool modEq = false,
                    unsigned index = 0,
                    bool onlyExist = false);
  /** remove inst match
   *
   * This removes (the suffix of) m starting at the given index from this trie.
   * It returns true if and only if this entry existed in this trie.
   * The domain of m is the bound variables of quantified formula q.
   */
  bool removeInstMatch(Node q, std::vector<Node>& m, unsigned index = 0);
  /** record instantiation lemma
   *
   * This records that the instantiation lemma lem corresponds to the entry
   * given by (the suffix of) m starting at the given index.
   */
  bool recordInstLemma(Node q,
                       std::vector<Node>& m,
                       Node lem,
                       unsigned index = 0);

  /** get instantiations
   *
   * This gets the set of instantiation lemmas that were recorded in this class
   * via calls to recordInstLemma. If useActive is true, we only add
   * instantiations that occur in active.
   */
  void getInstantiations(std::vector<Node>& insts,
                         Node q,
                         QuantifiersEngine* qe,
                         bool useActive,
                         std::vector<Node>& active)
  {
    std::vector<Node> terms;
    getInstantiations(insts, q, terms, qe, useActive, active);
  }
  /** get explanation for inst lemmas
   *
   * This gets the explanation for the instantiation lemmas in lems for
   * quantified formula q, for which this trie stores instantiation matches for.
   * For each instantiation lemma lem recording in this trie via calls to
   * recordInstLemma, we map lem to q in map quant, and lem to its corresponding
   * vector of terms in tvec.
   */
  void getExplanationForInstLemmas(
      Node q,
      const std::vector<Node>& lems,
      std::map<Node, Node>& quant,
      std::map<Node, std::vector<Node> >& tvec) const
  {
    std::vector<Node> terms;
    getExplanationForInstLemmas(q, terms, lems, quant, tvec);
  }

  /** print this class */
  void print(std::ostream& out,
             Node q,
             bool useActive,
             std::vector<Node>& active) const
  {
    std::vector<TNode> terms;
    print(out, q, terms, useActive, active);
  }

 private:
  /** the data */
  std::map<Node, CDInstMatchTrie*> d_data;
  /** is valid */
  context::CDO<bool> d_valid;
  /** helper for print
   * terms accumulates the path we are on in the trie.
   */
  void print(std::ostream& out,
             Node q,
             std::vector<TNode>& terms,
             bool useActive,
             std::vector<Node>& active) const;
  /** helper for get instantiations
   * terms accumulates the path we are on in the trie.
   */
  void getInstantiations(std::vector<Node>& insts,
                         Node q,
                         std::vector<Node>& terms,
                         QuantifiersEngine* qe,
                         bool useActive,
                         std::vector<Node>& active) const;
  /** helper for get explanation for inst lemma
   * terms accumulates the path we are on in the trie.
   */
  void getExplanationForInstLemmas(
      Node q,
      std::vector<Node>& terms,
      const std::vector<Node>& lems,
      std::map<Node, Node>& quant,
      std::map<Node, std::vector<Node> >& tvec) const;
  /** set instantiation lemma at this node in the trie */
  void setInstLemma(Node n)
  {
    d_data.clear();
    d_data[n] = NULL;
  }
  /** does this node of the trie store an instantiation lemma? */
  bool hasInstLemma() const { return !d_data.empty(); }
  /** get the instantiation lemma stored in this node of the trie */
  Node getInstLemma() const { return d_data.begin()->first; }
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
   * class. If modEq is true, we consider duplicates modulo the current
   * equalities stored in the active equality engine of quantifiers engine.
   */
  bool addInstMatch(QuantifiersEngine* qe,
                    Node q,
                    InstMatch& m,
                    bool modEq = false)
  {
    return d_imt.addInstMatch(qe, q, m, modEq, d_imtio);
  }
  /** returns true if this trie contains m
   *
   * This method returns true if the match m exists in this
   * class. If modEq is true, we consider duplicates modulo the current
   * equalities stored in the active equality engine of quantifiers engine.
   */
  bool existsInstMatch(QuantifiersEngine* qe,
                       Node q,
                       InstMatch& m,
                       bool modEq = false)
  {
    return d_imt.existsInstMatch(qe, q, m, modEq, d_imtio);
  }

 private:
  /** the ordering */
  InstMatchTrie::ImtIndexOrder* d_imtio;
  /** the data of this class */
  InstMatchTrie d_imt;
};

} /* CVC4::theory::inst namespace */
} /* CVC4::theory namespace */
} /* CVC4 namespace */

#endif /* CVC4__THEORY__QUANTIFIERS__INST_MATCH_H */
