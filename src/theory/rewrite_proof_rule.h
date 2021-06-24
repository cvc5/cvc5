/*********************                                                        */
/*! \file rewrite_proof_rule.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Rewrite proof rule data structure
 **/

#include "cvc5_private.h"

#ifndef CVC4__THEORY__REWRITE_PROOF_RULE__H
#define CVC4__THEORY__REWRITE_PROOF_RULE__H

#include <string>
#include <vector>

#include "expr/node.h"
#include "theory/rewriter/rewrites.h"

namespace cvc5 {
namespace theory {

/** Get DslPfRule from node */
bool getDslPfRule(TNode n, rewriter::DslPfRule& id);

/**
 * The definition of a (conditional) rewrite rule.
 */
class RewriteProofRule
{
 public:
  RewriteProofRule();
  /** initialize this rule */
  void init(const std::string& name, const std::vector<Node>& cond, Node conc);
  /** get name */
  const std::string& getName() const;
  /** Get variable list */
  const std::vector<Node>& getVarList() const;
  /** 
   * Is variable explicit? An explicit variable is one that does not occur
   * in a condition and thus its value must be specified in a proof.
   */
  bool isExplicitVar(Node v) const;
  /** Does this rule have conditions? */
  bool hasConditions() const;
  /** Get (declared) conditions */
  const std::vector<Node>& getConditions() const;
  /** Does this rule have side conditions? */
  bool hasSideConditions() const;
  /**
   * Get the conditions in context { vs -> ss }. This may involve running the
   * side conditions of this method.
   */
  bool getObligations(const std::vector<Node>& vs,
                      const std::vector<Node>& ss,
                      std::vector<Node>& vcs) const;
  /** Get conclusion of the rule */
  Node getConclusion() const;

 private:
  /**
   * Purify side conditions from term n, store introduced side condition
   * applications into scs.
   */
  Node purifySideConditions(Node n, std::vector<Node>& scs);
  /**
   * Run side conditions in context { vs -> ss }, add the resulting conditions
   * to check into the vector vcs.
   */
  bool runSideConditions(const std::vector<Node>& vs,
                         const std::vector<Node>& ss,
                         std::vector<Node>& vcs) const;
  /** The name of the rule */
  std::string d_name;
  /** The side conditions of the rule */
  std::vector<Node> d_scs;
  /** The conditions of the rule */
  std::vector<Node> d_cond;
  /** The obligation generator formulas of the rule */
  std::vector<Node> d_obGen;
  /** The conclusion of the rule (an equality) */
  Node d_conc;
  /** the ordered list of free variables */
  std::vector<Node> d_fvs;
  /** number of free variables */
  size_t d_numFv;
  /**
   * The free variables that do not occur in the conditions. These cannot be
   * "holes" in a proof.
   */
  std::map<Node, bool> d_noOccVars;
};

}  // namespace theory
}  // namespace cvc5

#endif /* CVC4__THEORY__REWRITE_PROOF_RULE__H */
