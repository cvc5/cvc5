/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Class for constructing inductive datatypes that correspond to
 * grammars that encode syntactic restrictions for SyGuS.
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__QUANTIFIERS__SYGUS_GRAMMAR_CONS_NEW_H
#define CVC5__THEORY__QUANTIFIERS__SYGUS_GRAMMAR_CONS_NEW_H

#include <map>
#include <vector>

#include "expr/node.h"
#include "expr/sygus_grammar.h"
#include "options/options.h"

namespace cvc5::internal {
namespace theory {
namespace quantifiers {

/**
 * Utility for constructing datatypes that correspond to syntactic restrictions.
 */
class SygusGrammarCons
{
 public:
  static TypeNode mkDefaultSygusType(const Options& opts,
                                     const TypeNode& range,
                                     const Node& bvl);
  static TypeNode mkDefaultSygusType(const Options& opts,
                                     const TypeNode& range,
                                     const Node& bvl,
                                     const std::vector<Node>& trules);

  static SygusGrammar mkDefaultGrammar(const Options& opts,
                                       const TypeNode& range,
                                       const Node& bvl);

  static SygusGrammar mkDefaultGrammar(const Options& opts,
                                       const TypeNode& range,
                                       const Node& bvl,
                                       const std::vector<Node>& trules);

  static SygusGrammar mkEmptyGrammar(const Options& opts,
                                     const TypeNode& range,
                                     const Node& bvl,
                                     const std::vector<Node>& trules);

  static void addDefaultRulesTo(const Options& opts,
                                SygusGrammar& g,
                                const Node& ntSym);

  static void addDefaultPredicateRulesTo(const Options& opts,
                                         SygusGrammar& g,
                                         const Node& ntSym,
                                         const Node& ntSymBool);

 private:
  static SygusGrammar mkEmptyGrammarInternal(
      const Options& opts,
      const TypeNode& range,
      const Node& bvl,
      const std::vector<Node>& trules,
      std::map<TypeNode, Node>& typeToNtSym);

  static void addDefaultRulesToInternal(
      const Options& opts,
      SygusGrammar& g,
      const Node& ntSym,
      const std::map<TypeNode, Node>& typeToNtSym);

  static void addDefaultPredicateRulesToInternal(
      const Options& opts,
      SygusGrammar& g,
      const Node& ntSym,
      const Node& ntSymBool,
      const std::map<TypeNode, Node>& typeToNtSym);
};

}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal

#endif