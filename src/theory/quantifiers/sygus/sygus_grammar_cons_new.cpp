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

#include "theory/quantifiers/sygus/sygus_grammar_cons_new.h"

#include "expr/node_algorithm.h"

namespace cvc5::internal {
namespace theory {
namespace quantifiers {

TypeNode SygusGrammarCons::mkDefaultSygusType(const Options& opts,
                                              const TypeNode& range,
                                              const Node& bvl)
{
  SygusGrammar g = mkDefaultGrammar(opts, range, bvl);
  return g.resolve();
}

TypeNode SygusGrammarCons::mkDefaultSygusType(const Options& opts,
                                              const TypeNode& range,
                                              const Node& bvl,
                                              const std::vector<Node>& trules)
{
  SygusGrammar g = mkDefaultGrammar(opts, range, bvl, trules);
  return g.resolve();
}

SygusGrammar SygusGrammarCons::mkDefaultGrammar(const Options& opts,
                                                const TypeNode& range,
                                                const Node& bvl)
{
  // default, include all variables as terminal rules
  std::vector<Node> trules;
  if (!bvl.isNull())
  {
    Assert(bvl.getKind() == BOUND_VARIABLE_LIST);
    trules.insert(trules.end(), bvl.begin(), bvl.end());
  }
  return mkDefaultGrammar(opts, range, bvl, trules);
}

SygusGrammar SygusGrammarCons::mkDefaultGrammar(const Options& opts,
                                                const TypeNode& range,
                                                const Node& bvl,
                                                const std::vector<Node>& trules)
{
  NodeManager* nm = NodeManager::currentNM();
  std::map<TypeNode, Node> typeToNtSym;
  std::map<TypeNode, Node>::iterator it;
  SygusGrammar g =
      mkEmptyGrammarInternal(opts, range, bvl, trules, typeToNtSym);

  // get the non-terminal for Booleans
  Node ntSymBool;
  TypeNode btype = nm->booleanType();
  it = typeToNtSym.find(btype);
  if (it != typeToNtSym.end())
  {
    ntSymBool = it->second;
  }

  // add the terminal rules
  for (const Node& r : trules)
  {
    TypeNode rt = r.getType();
    it = typeToNtSym.find(rt);
    Assert(it != typeToNtSym.end());
    g.addRule(it->second, r);
  }

  for (const std::pair<const TypeNode, Node>& gr : typeToNtSym)
  {
    // add rules for each type
    addDefaultRulesToInternal(opts, g, gr.second, typeToNtSym);
    // add predicates for the type to the Boolean grammar if it exists
    if (!ntSymBool.isNull() && !gr.first.isBoolean())
    {
      addDefaultPredicateRulesToInternal(
          opts, g, gr.second, ntSymBool, typeToNtSym);
    }
  }
  return g;
}

SygusGrammar SygusGrammarCons::mkEmptyGrammar(const Options& opts,
                                              const TypeNode& range,
                                              const Node& bvl,
                                              const std::vector<Node>& trules)
{
  std::map<TypeNode, Node> typeToNtSym;
  return mkEmptyGrammarInternal(opts, range, bvl, trules, typeToNtSym);
}

SygusGrammar SygusGrammarCons::mkEmptyGrammarInternal(
    const Options& opts,
    const TypeNode& range,
    const Node& bvl,
    const std::vector<Node>& trules,
    std::map<TypeNode, Node>& typeToNtSym)
{
  NodeManager* nm = NodeManager::currentNM();
  // get the variables
  std::vector<Node> vars;
  if (!bvl.isNull())
  {
    Assert(bvl.getKind() == BOUND_VARIABLE_LIST);
    vars.insert(vars.end(), bvl.begin(), bvl.end());
  }
  // collect the types we are considering, which is all component types of
  // the range type and the initial terminal rules. We also always include
  // Bool.
  std::unordered_set<TypeNode> types;
  for (const Node& r : trules)
  {
    expr::getComponentTypes(r.getType(), types, true);
  }
  expr::getComponentTypes(range, types, true);
  // always include Boolean
  TypeNode btype = nm->booleanType();
  types.insert(btype);
  // the range type comes first
  std::vector<TypeNode> tvec;
  tvec.push_back(range);
  for (const TypeNode& t : types)
  {
    if (t != range)
    {
      tvec.push_back(t);
    }
  }

  // construct the non-terminals
  std::vector<Node> ntSyms;
  for (const TypeNode& t : tvec)
  {
    Node a = nm->mkBoundVar("A", t);
    ntSyms.push_back(a);
    typeToNtSym[t] = a;
  }

  // contruct the grammar
  SygusGrammar ret(vars, ntSyms);
  return ret;
}

void SygusGrammarCons::addDefaultRulesTo(const Options& opts,
                                         SygusGrammar& g,
                                         const Node& ntSym)
{
}

void SygusGrammarCons::addDefaultPredicateRulesTo(const Options& opts,
                                                  SygusGrammar& g,
                                                  const Node& ntSym,
                                                  const Node& ntSymBool)
{
}

void SygusGrammarCons::addDefaultRulesToInternal(
    const Options& opts,
    SygusGrammar& g,
    const Node& ntSym,
    const std::map<TypeNode, Node>& typeToNtSym)
{
}

void SygusGrammarCons::addDefaultPredicateRulesToInternal(
    const Options& opts,
    SygusGrammar& g,
    const Node& ntSym,
    const Node& ntSymBool,
    const std::map<TypeNode, Node>& typeToNtSym)
{
  Assert(!ntSym.getType().isBoolean());
  Assert(ntSymBool.getType().isBoolean());
}

}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal
