/*********************                                                        */
/*! \file abstraction.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Liana Hadarean, Tim King, Mathias Preiner
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Bitvector theory.
 **
 ** Bitvector theory.
 **/

#include "cvc4_private.h"

#ifndef CVC4__THEORY__BV__ABSTRACTION_H
#define CVC4__THEORY__BV__ABSTRACTION_H

#include <unordered_map>
#include <unordered_set>

#include "expr/node.h"
#include "theory/substitutions.h"
#include "util/statistics_registry.h"

namespace CVC4 {
namespace theory {
namespace bv {

typedef std::vector<TNode> ArgsVec;

class AbstractionModule {

  struct Statistics {
    IntStat d_numFunctionsAbstracted;
    IntStat d_numArgsSkolemized;
    TimerStat d_abstractionTime;
    Statistics(const std::string& name);
    ~Statistics();
  };


  class ArgsTableEntry {
    std::vector<ArgsVec> d_data;
    unsigned d_arity;
  public:
    ArgsTableEntry(unsigned n)
      : d_arity(n)
    {}
    ArgsTableEntry()
      : d_arity(0)
    {}
    void addArguments(const ArgsVec& args);
    typedef std::vector<ArgsVec>::iterator iterator;

    iterator begin() { return d_data.begin(); }
    iterator end() { return d_data.end(); }
    unsigned getArity() { return d_arity; }
    unsigned getNumEntries() { return d_data.size(); }
    ArgsVec& getEntry(unsigned i)
    {
      Assert(i < d_data.size());
      return d_data[i];
    }
  };

  class ArgsTable {
    std::unordered_map<TNode, ArgsTableEntry, TNodeHashFunction > d_data;
    bool hasEntry(TNode signature) const;
  public:
    typedef std::unordered_map<TNode, ArgsTableEntry, TNodeHashFunction >::iterator iterator;
    ArgsTable() {}
    void addEntry(TNode signature, const ArgsVec& args);
    ArgsTableEntry& getEntry(TNode signature);
    iterator begin() { return d_data.begin(); }
    iterator end() { return d_data.end(); }
  };

  /**
   * Checks if one pattern is a generalization of the other
   *
   * @param s
   * @param t
   *
   * @return 1 if s :> t, 2 if s <: t, 0 if they equivalent and -1 if they are incomparable
   */
  static int comparePatterns(TNode s, TNode t);

  class LemmaInstantiatior {
    std::vector<TNode> d_functions;
    std::vector<int> d_maxMatch;
    ArgsTable& d_argsTable;
    context::Context* d_ctx;
    theory::SubstitutionMap d_subst;
    TNode d_conflict;
    std::vector<Node> d_lemmas;

    void backtrack(std::vector<int>& stack);
    int next(int val, int index);
    bool isConsistent(const std::vector<int>& stack);
    bool accept(const std::vector<int>& stack);
    void mkLemma();
  public:
    LemmaInstantiatior(const std::vector<TNode>& functions, ArgsTable& table, TNode conflict)
      : d_functions(functions)
      , d_argsTable(table)
      , d_ctx(new context::Context())
      , d_subst(d_ctx)
      , d_conflict(conflict)
      , d_lemmas()
    {
      Debug("bv-abstraction-gen") << "LemmaInstantiator conflict:" << conflict << "\n";
      // initializing the search space
      for (unsigned i = 0; i < functions.size(); ++i) {
        TNode func_op = functions[i].getOperator();
        // number of matches for this function
        unsigned maxCount = table.getEntry(func_op).getNumEntries();
        d_maxMatch.push_back(maxCount);
      }
    }

    void generateInstantiations(std::vector<Node>& lemmas);

  };

  typedef std::unordered_map<Node, std::vector<Node>, NodeHashFunction> NodeVecMap;
  typedef std::unordered_map<Node, TNode, NodeHashFunction> NodeTNodeMap;
  typedef std::unordered_map<TNode, TNode, TNodeHashFunction> TNodeTNodeMap;
  typedef std::unordered_map<Node, Node, NodeHashFunction> NodeNodeMap;
  typedef std::unordered_map<Node, TNode, NodeHashFunction> TNodeNodeMap;
  typedef std::unordered_set<TNode, TNodeHashFunction> TNodeSet;
  typedef std::unordered_map<unsigned, Node> IntNodeMap;
  typedef std::unordered_map<unsigned, unsigned> IndexMap;
  typedef std::unordered_map<unsigned, std::vector<Node> > SkolemMap;
  typedef std::unordered_map<TNode, unsigned, TNodeHashFunction > SignatureMap;

  ArgsTable d_argsTable;

  // mapping between signature and uninterpreted function symbol used to
  // abstract the signature
  NodeNodeMap d_signatureToFunc;
  NodeNodeMap d_funcToSignature;

  NodeNodeMap d_assertionToSignature;
  SignatureMap d_signatures;
  NodeNodeMap d_sigToGeneralization;
  TNodeSet d_skolems;

  // skolems maps
  IndexMap d_signatureIndices;
  SkolemMap d_signatureSkolems;

  void collectArgumentTypes(TNode sig, std::vector<TypeNode>& types, TNodeSet& seen);
  void collectArguments(TNode node, TNode sig, std::vector<Node>& args, TNodeSet& seen);
  void finalizeSignatures();
  Node abstractSignatures(TNode assertion);
  Node computeSignature(TNode node);

  bool isConjunctionOfAtoms(TNode node, TNodeSet& seen);

  TNode getGeneralization(TNode term);
  void storeGeneralization(TNode s, TNode t);

  // signature skolem stuff
  Node getGeneralizedSignature(Node node);
  Node getSignatureSkolem(TNode node);

  unsigned getBitwidthIndex(unsigned bitwidth);
  void resetSignatureIndex();
  Node computeSignatureRec(TNode, NodeNodeMap&);
  void storeSignature(Node signature, TNode assertion);
  bool hasSignature(Node node);

  Node substituteArguments(TNode signature, TNode apply, unsigned& i, TNodeTNodeMap& seen);

  // crazy instantiation methods
  void generateInstantiations(unsigned current,
                              std::vector<ArgsTableEntry>& matches,
                              std::vector<std::vector<ArgsVec> >& instantiations,
                              std::vector<std::vector<ArgsVec> >& new_instantiations);

  Node tryMatching(const std::vector<Node>& ss, const std::vector<TNode>& tt, TNode conflict);
  void makeFreshArgs(TNode func, std::vector<Node>& fresh_args);
  void makeFreshSkolems(TNode node, SubstitutionMap& map, SubstitutionMap& reverse_map);

  void skolemizeArguments(std::vector<Node>& assertions);
  Node reverseAbstraction(Node assertion, NodeNodeMap& seen);

  TNodeSet d_addedLemmas;
  TNodeSet d_lemmaAtoms;
  TNodeSet d_inputAtoms;
  void storeLemma(TNode lemma);

  Statistics d_statistics;

public:
  AbstractionModule(const std::string& name)
    : d_argsTable()
    , d_signatureToFunc()
    , d_funcToSignature()
    , d_assertionToSignature()
    , d_signatures()
    , d_sigToGeneralization()
    , d_skolems()
    , d_signatureIndices()
    , d_signatureSkolems()
    , d_addedLemmas()
    , d_lemmaAtoms()
    , d_inputAtoms()
    , d_statistics(name)
  {}
  /**
   * returns true if there are new uninterepreted functions symbols in the output
   *
   * @param assertions
   * @param new_assertions
   *
   * @return
   */
  bool applyAbstraction(const std::vector<Node>& assertions, std::vector<Node>& new_assertions);
  /**
   * Returns true if the node represents an abstraction predicate.
   *
   * @param node
   *
   * @return
   */
  bool isAbstraction(TNode node);
  /**
   * Returns the interpretation of the abstraction predicate.
   *
   * @param node
   *
   * @return
   */
  Node getInterpretation(TNode node);
  Node simplifyConflict(TNode conflict);
  void generalizeConflict(TNode conflict, std::vector<Node>& lemmas);
  void addInputAtom(TNode atom);
  bool isLemmaAtom(TNode node) const;
};

}
}
}

#endif
