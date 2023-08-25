/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Tim King, Mathias Preiner
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Quantifiers conflict find class.
 */

#include "cvc5_private.h"

#ifndef QUANT_CONFLICT_FIND
#define QUANT_CONFLICT_FIND

#include <ostream>
#include <vector>

#include "context/cdhashmap.h"
#include "context/cdlist.h"
#include "expr/node_trie.h"
#include "theory/quantifiers/inst_match.h"
#include "theory/quantifiers/quant_module.h"

namespace cvc5::internal {
namespace theory {
namespace quantifiers {

class QuantConflictFind;
class QuantInfo;

//match generator
class MatchGen : protected EnvObj {
  friend class QuantInfo;

 public:
  MatchGen(Env& env, QuantConflictFind* p, QuantInfo* qi, Node n, bool isVar = false);

  //type of the match generator
  enum {
    typ_invalid,
    typ_ground,
    typ_pred,
    typ_eq,
    typ_formula,
    typ_var,
    typ_bool_var,
    typ_tconstraint,
    typ_tsym,
  };
  void debugPrintType( const char * c, short typ);

  bool d_tgt;
  bool d_tgt_orig;
  bool d_wasSet;
  Node d_n;
  std::vector<std::unique_ptr<MatchGen> > d_children;
  short d_type;
  bool d_type_not;
  /** reset round
   *
   * Called once at the beginning of each full/last-call effort, prior to
   * processing this match generator. This method returns false if the reset
   * failed, e.g. if a conflict was encountered during term indexing.
   */
  bool reset_round();
  void reset(bool tgt);
  bool getNextMatch();
  bool isValid() const { return d_type != typ_invalid; }
  void setInvalid();
  Node getNode() const { return d_n; }

  // is this term treated as UF application?
  static bool isHandledBoolConnective( TNode n );
  static bool isHandledUfTerm( TNode n );
  //can this node be handled by the algorithm
  static bool isHandled( TNode n );

 private:
  // determine variable order
  void determineVariableOrder(std::vector<size_t>& bvars);
  void collectBoundVar(Node n,
                       std::vector<int>& cbvars,
                       std::map<Node, bool>& visited,
                       bool& hasNested);
  size_t getNumChildren() const { return d_children.size(); }
  MatchGen* getChild(size_t i) const
  {
    return d_children[d_children_order[i]].get();
  }
  bool doMatching();
  /** The parent who owns this class */
  QuantConflictFind* d_parent;
  /** Quantifier info of the parent */
  QuantInfo* d_qi;
  // current children information
  int d_child_counter;
  bool d_use_children;
  // children of this object
  std::vector<size_t> d_children_order;
  // current matching information
  std::vector<TNodeTrie*> d_qn;
  std::vector<std::map<TNode, TNodeTrie>::iterator> d_qni;
  // for matching : each index is either a variable or a ground term
  size_t d_qni_size;
  std::map<size_t, size_t> d_qni_var_num;
  std::map<size_t, TNode> d_qni_gterm;
  std::map<size_t, size_t> d_qni_bound;
  std::vector<size_t> d_qni_bound_except;
  std::map<size_t, TNode> d_qni_bound_cons;
  std::map<size_t, size_t> d_qni_bound_cons_var;
  std::map<size_t, size_t>::iterator d_binding_it;
  bool d_matched_basis;
  bool d_binding;
  // int getVarBindingVar();
  std::map<size_t, Node> d_ground_eval;
};

//info for quantifiers
class QuantInfo : protected EnvObj
{
 public:
  using VarMgMap = std::map<size_t, std::unique_ptr<MatchGen>>;
  QuantInfo(Env& env,
            QuantifiersState& qs,
            TermRegistry& tr,
            QuantConflictFind* p,
            Node q);
  ~QuantInfo();
  /** get quantified formula */
  Node getQuantifiedFormula() const;
  bool isBaseMatchComplete();
  /** Get quantifiers inference manager */
  QuantifiersInferenceManager& getInferenceManager();
  std::vector<TNode> d_vars;
  std::vector<TypeNode> d_var_types;
  std::map<TNode, size_t> d_var_num;
  std::vector<size_t> d_tsym_vars;
  int getVarNum(TNode v) const;
  bool isVar(TNode v) const { return d_var_num.find(v) != d_var_num.end(); }
  size_t getNumVars() const { return d_vars.size(); }
  TNode getVar(size_t i) const { return d_vars[i]; }
  VarMgMap::const_iterator var_mg_find(size_t i) const
  {
    return d_var_mg.find(i);
  }
  VarMgMap::const_iterator var_mg_end() const { return d_var_mg.end(); }
  bool containsVarMg(size_t i) const { return var_mg_find(i) != var_mg_end(); }
  bool matchGeneratorIsValid() const { return d_mg->isValid(); }
  bool getNextMatch() { return d_mg->getNextMatch(); }
  bool reset_round();
  size_t getCurrentRepVar(size_t v);
  TNode getCurrentValue( TNode n );
  TNode getCurrentExpValue( TNode n );
  bool getCurrentCanBeEqual(size_t v, TNode n, bool chDiseq = false);
  int addConstraint(size_t v, TNode n, bool polarity);
  int addConstraint(size_t v, TNode n, int vn, bool polarity, bool doRemove);
  bool setMatch(size_t v, TNode n, bool isGroundRep, bool isGround);
  void unsetMatch(size_t v);
  bool isMatchSpurious();
  bool isTConstraintSpurious(const std::vector<Node>& terms);
  bool entailmentTest(Node lit, bool chEnt = true);
  bool completeMatch(std::vector<size_t>& assigned, bool doContinue = false);
  void revertMatch(const std::vector<size_t>& assigned);
  void debugPrintMatch(const char* c) const;
  bool isConstrainedVar(size_t v);
  void getMatch( std::vector< Node >& terms );

  // current constraints
  std::vector<TNode> d_match;
  std::vector<TNode> d_match_term;
  std::map<size_t, std::map<TNode, size_t> > d_curr_var_deq;
  std::map<Node, bool> d_tconstraints;

 private:
  void registerNode(Node n, bool hasPol, bool pol, bool beneathQuant = false);
  void flatten(Node n, bool beneathQuant);
  void getPropagateVars(std::vector<TNode>& vars,
                        TNode n,
                        bool pol,
                        std::map<TNode, bool>& visited);
  /** Reference to the quantifiers state */
  QuantifiersState& d_qs;
  /** The parent who owns this class */
  QuantConflictFind* d_parent;
  /** An instantiation match */
  InstMatch d_instMatch;
  std::unique_ptr<MatchGen> d_mg;
  Node d_q;
  VarMgMap d_var_mg;
  // for completing match
  std::vector<size_t> d_unassigned;
  std::vector<TypeNode> d_unassigned_tn;
  size_t d_unassigned_nvar;
  size_t d_una_index;
  std::vector<int> d_una_eqc_count;
  // optimization: track which arguments variables appear under UF terms in
  std::map<size_t, std::map<TNode, std::vector<size_t> > > d_var_rel_dom;
  // optimization: number of variables set, to track when we can stop
  std::unordered_set<size_t> d_vars_set;
  std::vector<Node> d_extra_var;
};

class QuantConflictFind : public QuantifiersModule
{
  friend class MatchGen;
  friend class QuantInfo;
 public:
  QuantConflictFind(Env& env,
                    QuantifiersState& qs,
                    QuantifiersInferenceManager& qim,
                    QuantifiersRegistry& qr,
                    TermRegistry& tr);

  /** register quantifier */
  void registerQuantifier(Node q) override;
  /** needs check */
  bool needsCheck(Theory::Effort level) override;
  /** reset round */
  void reset_round(Theory::Effort level) override;
  /** check
   *
   * This method attempts to construct a conflicting or propagating instance.
   * If such an instance exists, then it makes a call to
   * Instantiation::addInstantiation.
   */
  void check(Theory::Effort level, QEffort quant_e) override;

  /** statistics class */
  class Statistics {
  public:
    IntStat d_inst_rounds;
    IntStat d_entailment_checks;
    Statistics(StatisticsRegistry& sr);
  };
  Statistics d_statistics;
  /** Identify this module */
  std::string identify() const override { return "QcfEngine"; }
  /** is n a propagating instance?
   *
   * A propagating instance is any formula that consists of Boolean connectives,
   * equality, quantified formulas, and terms that exist in the current
   * context (those in the master equality engine).
   *
   * Notice the distinction that quantified formulas that do not appear in the
   * current context are considered to be legal in propagating instances. This
   * choice is significant for TPTP, where a net of ~200 benchmarks are gained
   * due to this decision.
   *
   * Propagating instances are the second most useful kind of instantiation
   * after conflicting instances and are used as a second effort in the
   * algorithm performed by this class.
   */
  bool isPropagatingInstance(Node n) const;

  enum Effort : unsigned
  {
    EFFORT_CONFLICT,
    EFFORT_PROP_EQ,
    EFFORT_INVALID,
  };
  void setEffort(Effort e) { d_effort = e; }

  bool atConflictEffort() const
  {
    return d_effort == QuantConflictFind::EFFORT_CONFLICT;
  }

  TNode getZero(TypeNode tn, Kind k);

 private:
  /** check quantified formula
   *
   * This method is called by the above check method for each quantified
   * formula q. It attempts to find a conflicting or propagating instance for
   * q, depending on the effort level (d_effort).
   *
   * isConflict: this is set to true if we discovered a conflicting instance.
   * This flag may be set instead of d_conflict if --qcf-all-conflict is true,
   * in which we continuing adding all conflicts.
   * addedLemmas: tracks the total number of lemmas added, and is incremented by
   * this method when applicable.
   */
  void checkQuantifiedFormula(Node q, bool& isConflict, unsigned& addedLemmas);
  void debugPrint(const char* c) const;
  void debugPrintQuant(const char* c, Node q) const;
  void debugPrintQuantBody(const char* c,
                           Node q,
                           Node n,
                           bool doVarNum = true) const;
  void setIrrelevantFunction(TNode f);
  // for debugging
  std::vector<Node> d_quants;
  std::map<Node, size_t> d_quant_id;
  /** Map from quantified formulas to their info class to compute instances */
  std::map<Node, std::unique_ptr<QuantInfo> > d_qinfo;
  /** Map from type -> list(eqc) of that type */
  std::map<TypeNode, std::vector<TNode> > d_eqcs;
  /** Are we in conflict? */
  context::CDO<bool> d_conflict;
  /** Zeros for (type, kind) pairs */
  std::map<std::pair<TypeNode, Kind>, Node> d_zero;
  // for storing nodes created during t-constraint solving (prevents memory
  // leaks)
  std::vector<Node> d_tempCache;
  // optimization: list of quantifiers that depend on ground function
  // applications
  std::map<TNode, std::vector<Node> > d_func_rel_dom;
  std::map<TNode, bool> d_irr_func;
  std::map<Node, bool> d_irr_quant;
  /** The current effort */
  Effort d_effort;
};

std::ostream& operator<<(std::ostream& os, const QuantConflictFind::Effort& e);

}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal

#endif
