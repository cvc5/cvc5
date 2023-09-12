/******************************************************************************
 * Top contributors (to current version):
 *   Abdalrhman Mohamed, Andrew Reynolds
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
  /** Input variables to the corresponding function/invariant to synthesize.*/
  std::vector<Node> d_sygusVars;
  /** The non-terminal symbols of this grammar. */
  std::vector<Node> d_ntSyms;
  /** Mapping from non-terminal symbols to their production rules. */
  std::unordered_map<Node, std::vector<Node>> d_rules;
  /** The datatype type constructed by this grammar. */
  TypeNode d_datatype;
};

}  // namespace cvc5::internal

#endif
