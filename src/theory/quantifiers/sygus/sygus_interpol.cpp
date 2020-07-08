/*********************                                                        */
/*! \file sygus_interpol.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Ying Sheng
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Implementation of sygus interpolation utility, which
 ** transforms an input of axioms and conjecture into an interpolation problem,
 *and solve it.
 **/

#include "theory/quantifiers/sygus/sygus_interpol.h"

#include "expr/datatype.h"
#include "expr/dtype.h"
#include "expr/node_algorithm.h"
#include "expr/sygus_datatype.h"
#include "options/smt_options.h"
#include "printer/sygus_print_callback.h"
#include "theory/datatypes/sygus_datatype_utils.h"
#include "theory/quantifiers/quantifiers_attributes.h"
#include "theory/quantifiers/quantifiers_rewriter.h"
#include "theory/quantifiers/sygus/sygus_grammar_cons.h"
#include "theory/quantifiers/term_util.h"
#include "theory/rewriter.h"

namespace CVC4 {
namespace theory {
namespace quantifiers {

SygusInterpol::SygusInterpol() {}

SygusInterpol::SygusInterpol(LogicInfo logic) : d_logic(logic) {}

void SygusInterpol::collectSymbols(const std::vector<Node>& axioms,
                                   const Node& conj)
{
}

void SygusInterpol::createVariables(bool needsShared)
{
}

std::map<TypeNode, std::unordered_set<Node, NodeHashFunction> > getIncludeCons(
    const std::vector<Node>& assumptions, const Node& conclusion)
{
  std::map<TypeNode, std::unordered_set<Node, NodeHashFunction> > result =
      std::map<TypeNode, std::unordered_set<Node, NodeHashFunction> >();
  return result;
}

TypeNode SygusInterpol::setSynthGrammar(const TypeNode& itpGType,
                                        const std::vector<Node>& axioms,
                                        const Node& conj)
{
  TypeNode itpGTypeS;
  return itpGTypeS;
}

Node SygusInterpol::mkPredicate(const std::string& name)
{
  Node itp;
  return itp;
}

void SygusInterpol::mkSygusConjecture(Node itp,
                                      const std::vector<Node>& axioms,
                                      const Node& conj)
{
}

bool SygusInterpol::findInterpol(Expr& interpol, Node itp)
{
  return false;
}

bool SygusInterpol::SolveInterpolation(const std::string& name,
                                       const std::vector<Node>& axioms,
                                       const Node& conj,
                                       const TypeNode& itpGType,
                                       Expr& interpol)
{
  return false;
}

}  // namespace quantifiers
}  // namespace theory
}  // namespace CVC4
