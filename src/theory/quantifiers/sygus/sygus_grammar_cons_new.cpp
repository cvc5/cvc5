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

namespace cvc5::internal {
namespace theory {
namespace quantifiers {

TypeNode SygusGrammarCons::mkDefaultSygusType(
    const Options& opts,
    const TypeNode& range,
    const Node& bvl)
{
  SygusGrammar g = mkDefaultGrammar(opts, range, bvl);
  return g.resolve();
}

TypeNode SygusGrammarCons::mkDefaultSygusType(
    const Options& opts,
    const TypeNode& range,
    const Node& bvl,
    const std::vector<Node>& trules)
{
  SygusGrammar g = mkDefaultGrammar(opts, range, bvl, trules);
  return g.resolve();
}

SygusGrammar SygusGrammarCons::mkDefaultGrammar(
    const Options& opts,
    const TypeNode& range,
    const Node& bvl)
{
  // default, include all variables as terminal rules
  std::vector<Node> trules;
  if (!bvl.isNull())
  {
    Assert (bvl.getKind()==BOUND_VARIABLE_LIST);
    trules.insert(trules.end(), bvl.begin(), bvl.end());
  }
  return mkDefaultGrammar(opts, range, bvl, trules);
}

SygusGrammar SygusGrammarCons::mkDefaultGrammar(
    const Options& opts,
    const TypeNode& range,
    const Node& bvl,
    const std::vector<Node>& trules)
{
  std::map<TypeNode, Node> typeToNtSym;
  SygusGrammar g = mkEmptyGrammarInternal(opts, range, bvl, trules, typeToNtSym);
  // add the terminal rules
  std::map<TypeNode, Node>::iterator it;
  for (const Node& r : trules)
  {
    TypeNode rt = r.getType();
    it = typeToNtSym.fidn(rt);
    Assert (it != typeToNtSym.end());
    g.addRule(it->second, r);
  }
  // add the builtin 
}

SygusGrammar SygusGrammarCons::mkEmptyGrammar(
    const Options& opts,
    const TypeNode& range,
    const Node& bvl,
     const std::vector<Node>& trules)
{
  std::map<TypeNode, Node> typeToNtSym;
  return mkEmptyGrammarInternal(opts, range, bvl, trules, typeToNtSym);
}

SygusGrammar SygusGrammarCons::mkEmptyGrammar(
    const Options& opts,
    const TypeNode& range,
    const Node& bvl,
     const std::vector<Node>& trules,
    std::map<TypeNode, Node>* typeToNtSym)
{
  // get the variables
  std::vector<Node> vars;
  if (!bvl.isNull())
  {
    Assert (bvl.getKind()==BOUND_VARIABLE_LIST);
    vars.insert(vars.end(), bvl.begin(), bvl.end());
  }
  // collect the types we are considering
  std::unordered_set<TypeNode> types;
  for (const Node& r : trules)
  {
    expr::getSubfieldTypes(r.getType(), types, true);
  }
  expr::getSubfieldTypes(range, types, true);
  
  // construct the non-terminals
  std::vector<Node> ntSyms;
  for (const TypeNode& t : types)
  {
    Node a = nm->mkBoundVar("A", t);
    ntSyms.push_back(a);
    typeToNtSym[t] = a;
  }
  
  // contruct the grammar
  SygusGrammar ret(vars, ntSyms);
  return ret;
}

void SygusGrammarCons::addDefaultRulesTo(
    const Options& opts,
    SygusGrammar& g,
    const Node& ntSym)
{
  
}

 void SygusGrammarCons::addDefaultPredicateRulesTo(
     const Options& opts,
     SygusGrammar& g,
     const Node& ntSym,
     const Node& ntSymBool)
 {
   
 }
 
}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal

