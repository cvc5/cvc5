/******************************************************************************
 * Top contributors (to current version):
 *   Abdalrhman Mohamed
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * A class for constructing SyGuS grammars.
 */
#include "cvc5_private.h"

#ifndef CVC5__EXPR__SYGUS_GRAMMAR_H
#define CVC5__EXPR__SYGUS_GRAMMAR_H

#include <vector>

#include "expr/node.h"
#include "expr/sygus_datatype.h"

namespace cvc5::internal {

/**
 * A Sygus Grammar. This class can be used to define a context-free grammar
 * of Nodes. Its interface coincides with the definition of grammars
 * (``GrammarDef``) in the SyGuS IF 2.1 standard.
 */
class SygusGrammar
{
 public:
  /**
   * Constructor.
   * @param sygusVars The input variables to synth-fun/synth-var.
   * @param ntSyms The non-terminals of this grammar.
   */
  SygusGrammar(const std::vector<Node>& sygusVars,
               const std::vector<Node>& ntSyms);

  /**
   * Add \p rule to the set of rules corresponding to \p ntSym.
   * @param ntSym The non-terminal to which the rule is added.
   * @param rule The rule to add.
   */
  void addRule(const Node& ntSym, const Node& rule);

  /**
   * Add \p rules to the set of rules corresponding to \p ntSym.
   * @param ntSym The non-terminal to which the rules are added.
   * @param rules The rules to add.
   */
  void addRules(const Node& ntSym, const std::vector<Node>& rules);

  /**
   * Allow \p ntSym to be an arbitrary constant of type \p tn.
   * @param ntSym The non-terminal allowed to be any constant.
   * @param tn The type of allowed constants.
   */
  void addAnyConstant(const Node& ntSym, const TypeNode& tn);

  /**
   * Allow \p ntSym to be any input variable to corresponding
   * synth-fun/synth-inv with the same type as \p ntSym.
   * @param ntSym The non-terminal allowed to be any input variable.
   */
  void addAnyVariable(const Node& ntSym);

  /**
   * Remove \p rule from the set of rules corresponding to \p ntSym.
   * @param ntSym The non-terminal from which the rule is removed.
   * @param rule The rule to remove. This must be a rule that occurs
   * in the list of rules for ntSym.
   */
  void removeRule(const Node& ntSym, const Node& rule);

  /**
   * @return The resolved datatype of the Start symbol of the grammar.
   */
  TypeNode resolve(bool allowAny = false);

  /**
   * @return whether or not this grammar is resolved.
   */
  bool isResolved();

  /**
   * @return The sygus variables of this grammar.
   */
  const std::vector<Node>& getSygusVars() const;

  /**
   * @return The non-terminal symbols of this grammar.
   */
  const std::vector<Node>& getNtSyms() const;

  /**
   * @return The rules for non-terminal ntSym
   */
  const std::vector<Node>& getRulesFor(const Node& ntSym) const;

  /**
   * @return A string representation of this grammar.
   */
  std::string toString() const;

 private:
  /**
   * Add \p rule to the set of rules corresponding to \p ntSym.
   * @param ntSym The non-terminal to which the rule is added.
   * @param rule The rule to add.
   */
  void addRuleInternal(const Node& ntSym, const Node& rule);
  /**
   * Purify SyGuS grammar node.
   *
   * This returns a node where all occurrences of non-terminal symbols (those
   * in the domain of \p ntsToUnres) are replaced by fresh variables. For
   * each variable replaced in this way, we add the fresh variable it is
   * replaced with to \p args, and the unresolved types corresponding to the
   * non-terminal symbol to \p cargs (constructor args). In other words,
   * \p args contains the free variables in the node returned by this method
   * (which should be bound by a lambda), and \p cargs contains the types of
   * the arguments of the sygus constructor.
   *
   * @param n The node to purify.
   * @param args The free variables in the node returned by this method.
   * @param cargs The types of the arguments of the sygus constructor.
   * @return The purfied node.
   */
  Node purifySygusGNode(const Node& n,
                        std::vector<Node>& args,
                        std::vector<TypeNode>& cargs) const;
  /** The rules */
  std::unordered_map<Node, std::vector<Node>> d_rules;
  /** Input variables to the corresponding function/invariant to synthesize.*/
  std::vector<Node> d_sygusVars;
  /** The non-terminal symbols of this grammar. */
  std::vector<Node> d_ntSyms;
  /** Mapping from non-terminal symbols to their production rules. */
  std::unordered_map<Node, SygusDatatype> d_sdts;
  /** Mapping from non-terminals to their unresolved types. */
  std::unordered_map<Node, TypeNode> d_ntsToUnres;
  /** The datatype type constructed by this grammar. */
  TypeNode d_datatype;
};

}  // namespace cvc5::internal

#endif
