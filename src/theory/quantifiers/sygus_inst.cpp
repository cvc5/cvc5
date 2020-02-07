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
#include "theory/datatypes/theory_datatypes_utils.h"
#include "theory/quantifiers/sygus/sygus_enumerator.h"
#include "theory/quantifiers/sygus/sygus_grammar_cons.h"
#include "theory/quantifiers/sygus/synth_engine.h"
#include "theory/quantifiers_engine.h"

namespace CVC4 {
namespace theory {
namespace quantifiers {

SygusInst::SygusInst(QuantifiersEngine* qe)
    : QuantifiersModule(qe), d_quant_vars(), d_enumerators()
{
}

// Note: Called once per q (context-independent initialization)
void SygusInst::registerQuantifier(Node q)
{
  Trace("sygus-inst") << "Register " << q << std::endl;

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
    Trace("sygus-inst") << "Found symbol: " << sym << std::endl;
  }

  Assert(d_quant_vars.find(q) == d_quant_vars.end());
  auto& vars = d_quant_vars[q];
  expr::getVariables(q, vars);
  NodeManager* nm = NodeManager::currentNM();
  for (const Node& var : vars)
  {
    TypeNode tn = CegGrammarConstructor::mkSygusDefaultType(var.getType(),
                                                            var,
                                                            var.toString(),
                                                            extra_cons,
                                                            exclude_cons,
                                                            include_cons,
                                                            term_irrelevant);
    // std::cout << "tn for " << var << ": " << tn.getDType() << std::endl;
    Trace("sygus-inst") << "Construct (default) datatype for " << var
                        << std::endl;
    d_enumerators.emplace(std::make_pair(
        var,
        new SygusEnumerator(d_quantEngine->getTermDatabaseSygus(), nullptr)));
    d_enumerators.at(var)->initialize(nm->mkSkolem("", tn));
  }
}

// Note: Called once per SAT context
void SygusInst::preRegisterQuantifier(Node q)
{
  // std::cout << identify() << "::preRegister: " << q << std::endl;
}

void SygusInst::check(Theory::Effort e, QEffort quant_e)
{
  Trace("sygus-inst") << "Check " << e << ", " << quant_e << std::endl;

  if (quant_e != QEFFORT_STANDARD) return;

  FirstOrderModel* model = d_quantEngine->getModel();
  Instantiate* inst = d_quantEngine->getInstantiate();
  uint32_t nasserted = model->getNumAssertedQuantifiers();
  for (uint32_t i = 0; i < nasserted; ++i)
  {
    Node q = model->getAssertedQuantifier(i);
    if (!model->isQuantifierActive(q))
    {
      continue;
    }
    Trace("sygus-inst") << "Active: " << q << std::endl;
    Assert(d_quant_vars.find(q) != d_quant_vars.end());

    std::vector<Node> terms;
    for (const TNode& var : d_quant_vars[q])
    {
      Assert(d_enumerators.find(var) != d_enumerators.end());
      SygusEnumerator* senum = d_enumerators.at(var).get();
      if (senum == nullptr)
      {
        continue;
      }

      Trace("sygus-inst") << "Enumerate variable " << var << std::endl;
      for (size_t j = 0; j < 10; ++j)
      {
        Node n = senum->getCurrent();

        /* Enumerator finished. */
        if (!senum->increment())
        {
          Trace("sygus-inst") << "Enumerator finished for " << var << std::endl;
          d_enumerators.at(var).reset();
          break;
        }

        if (n.isNull())
        {
          continue;
        }
        Trace("sygus-inst-enum")
            << "enum: " << datatypes::utils::sygusToBuiltin(n) << std::endl;
      }
    }

    // if (inst->addInstantiation(q, terms))
    //{
    //}
  }
}

}  // namespace quantifiers
}  // namespace theory
}  // namespace CVC4
