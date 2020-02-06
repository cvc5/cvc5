/*********************                                                        */
/*! \file sygus_inst.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Mathias Preiner
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief SyGuS instantiator class.
 **/

#include "theory/quantifiers/sygus_inst.h"

#include <sstream>
#include <unordered_set>

#include "expr/node_algorithm.h"
#include "theory/quantifiers/sygus/sygus_grammar_cons.h"
#include "theory/quantifiers_engine.h"

namespace CVC4 {
namespace theory {
namespace quantifiers {

SygusInst::SygusInst(QuantifiersEngine* qe)
    : QuantifiersModule(qe), d_var_types()
{
}

// Note: Called once per q (context-independent initialization)
void SygusInst::registerQuantifier(Node q)
{
  std::cout << identify() << "::register: " << q << std::endl;

  std::map<TypeNode, std::unordered_set<Node, NodeHashFunction>> extra_cons;
  std::map<TypeNode, std::unordered_set<Node, NodeHashFunction>> exclude_cons;
  std::map<TypeNode, std::unordered_set<Node, NodeHashFunction>> include_cons;
  std::unordered_set<Node, NodeHashFunction> term_irrelevant;

  std::unordered_set<Node, NodeHashFunction> symbols;
  expr::getSymbols(q, symbols);
  for (const TNode& sym : symbols)
  {
    TypeNode tn = sym.getType();
    extra_cons[tn].insert(sym);
    std::cout << "sym: " << sym << std::endl;
  }

  for (const Node& var : q[0])
  {
    TypeNode tn = CegGrammarConstructor::mkSygusDefaultType(var.getType(),
                                                            var,
                                                            "",
                                                            extra_cons,
                                                            exclude_cons,
                                                            include_cons,
                                                            term_irrelevant);
    std::cout << "tn: " << tn << " " << tn.isDatatype()
              << tn.getDType().isSygus() << std::endl;
    std::cout << tn.getDType() << std::endl;
    d_var_types[var] = tn;
  }
}

// Note: Called once per SAT context
void SygusInst::preRegisterQuantifier(Node q)
{
  std::cout << identify() << "::preRegister: " << q << std::endl;
}

void SygusInst::check(Theory::Effort e, QEffort quant_e)
{
  std::cout << identify() << "::check " << e << ", " << quant_e << std::endl;

  // Notes:
  //
  // * check active quantifiers via FirstOrderModel d_quantEngine->getModel()
  //
}

}  // namespace quantifiers
}  // namespace theory
}  // namespace CVC4
