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
    : QuantifiersModule(qe), d_quantifiers(), d_inst_pools(), d_evaluator()
{
}

bool SygusInst::needsCheck(Theory::Effort e)
{
  return e >= Theory::EFFORT_LAST_CALL;
}

QuantifiersModule::QEffort SygusInst::needsModel(Theory::Effort e)
{
  return QEFFORT_STANDARD;
}

// Note: Called once per q (context-independent initialization)
void SygusInst::registerQuantifier(Node q)
{
  Trace("sygus-inst") << "Register " << q << std::endl;

  std::map<TypeNode, std::unordered_set<Node, NodeHashFunction>> extra_cons;
  std::map<TypeNode, std::unordered_set<Node, NodeHashFunction>> exclude_cons;
  std::map<TypeNode, std::unordered_set<Node, NodeHashFunction>> include_cons;
  std::unordered_set<Node, NodeHashFunction> term_irrelevant;

  Assert(d_quantifiers.find(q) == d_quantifiers.end());
  // auto& quants = d_quantifiers[q];
  std::vector<Node> quants;
  TermUtil::computeQuantContains(q, quants);

  // TODO: Right now we can't handle nested quantifiers yet
  if (quants.size() > 1)
  {
    Trace("sygus-inst") << "Skip: unsupported nested quantifiers." << std::endl;
    return;
  }
  // TODO: Right now we can't handle multiple variables
  else if (quants.size() == 1 && quants[0][0].getNumChildren() > 1)
  {
    Trace("sygus-inst") << "Skip: unsupported multiple variables." << std::endl;
    return;
  }

  d_quantifiers.emplace(std::make_pair(q, quants));

  std::unordered_set<Node, NodeHashFunction> syms;
  expr::getSymbols(q, syms);
  for (const TNode& var : syms)
  {
    TypeNode tn = var.getType();
    extra_cons[tn].insert(var);
    Trace("sygus-inst") << "Found symbol: " << var << std::endl;
  }

  TermDbSygus* db = d_quantEngine->getTermDatabaseSygus();
  for (const TNode& quant : quants)
  {
    Trace("sygus-inst") << "Process variables of " << quant << std::endl;
    for (const Node& var : quant[0])
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

      d_inst_pools[var].initialize(db, tn);
    }
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

    // TODO: We can't handle all quantifiers right now (nested, or more
    // variables)
    if (d_quantifiers.find(q) == d_quantifiers.end())
    {
      continue;
    }

    auto& quants = d_quantifiers.at(q);

    Trace("sygus-inst") << "Active: " << q << std::endl;

    std::vector<Node> args, vals;
    std::unordered_set<Node, NodeHashFunction> symbols;
    expr::getSymbols(q, symbols);
    for (const TNode& sym : symbols)
    {
      args.push_back(sym);
      vals.push_back(model->getValue(sym));
      Trace("sygus-inst") << "Model for " << sym << ": " << model->getValue(sym)
                          << std::endl;
    }

    for (const TNode& quant : quants)
    {
      bool do_inst = true;
      std::vector<Node> terms;

      /* Try to synthesize/find term for each variable.
       * Note: Currently if we can't find a term for a variable, we don't
       *       instantiate the quantifier at all.
       */
      for (const TNode& var : quant[0])
      {
        Assert(d_inst_pools.find(var) != d_inst_pools.end());
        InstPool& pool = d_inst_pools.at(var);

        if (pool.done())
        {
          Trace("sygus-inst") << "Enumerator finished for " << var << std::endl;
          do_inst = false;
          break;
        }

        Trace("sygus-inst")
            << "Find candidate for variable " << var << std::endl;
        Trace("sygus-inst") << "Check enumerated pool" << std::endl;
        Node term;
        for (const TNode& t : pool.getTerms())
        {
          if (checkCandidate(q[1], var, t, args, vals))
          {
            Trace("sygus-inst")
                << "Found existing candidate: " << t << std::endl;
            term = t;
            break;
          }
        }

        if (term.isNull())
        {
          Trace("sygus-inst") << "No existing candidate found" << std::endl;
        }

        // TODO: This loop can run a long time, restrict to N iterations?
        while (term.isNull())
        {
          TNode t = pool.next();

          if (t.isNull())
          {
            Assert(pool.done());
            break;
          }

          if (checkCandidate(q[1], var, t, args, vals))
          {
            Trace("sygus-inst") << "Found new candidate: " << t << std::endl;
            term = t;
            break;
          }
          else
          {
            Trace("sygus-inst-enum")
                << "Candidate not used: " << t << std::endl;
          }
        }

        if (term.isNull())
        {
          do_inst = false;
          break;
        }

        terms.push_back(term);
      }

      if (do_inst && inst->addInstantiation(q, terms, true))
      {
        Trace("sygus-inst") << "Instantiate " << q << std::endl;
      }
    }
  }
}

bool SygusInst::checkCandidate(TNode body,
                               TNode x,
                               TNode t,
                               std::vector<Node>& args,
                               std::vector<Node>& vals)
{
  Node val = d_evaluator.eval(t, args, vals);

  args.push_back(x);
  vals.push_back(val);

  Node fval = d_evaluator.eval(body, args, vals);

  args.pop_back();
  vals.pop_back();

  if (!fval.getConst<bool>())
  {
    return true;
  }
  return false;
}

/* InstPool */

SygusInst::InstPool::InstPool() : d_done(false), d_enumerator(), d_terms() {}

void SygusInst::InstPool::initialize(TermDbSygus* db, TypeNode& tn)
{
  d_enumerator.reset(new SygusEnumerator(db, nullptr));
  d_enumerator->initialize(NodeManager::currentNM()->mkSkolem("", tn));
}

bool SygusInst::InstPool::done() { return d_done; }

TNode SygusInst::InstPool::next()
{
  Node cur;
  // TODO: We may not want to skip all null terms.
  do
  {
    cur = d_enumerator->getCurrent();
    if (!d_enumerator->increment())
    {
      d_done = true;
      break;
    }
  } while (cur.isNull());

  if (!cur.isNull())
  {
    cur = datatypes::utils::sygusToBuiltin(cur);
    d_terms.push_back(cur);
  }

  return cur;
}

const std::vector<Node>& SygusInst::InstPool::getTerms() { return d_terms; }

}  // namespace quantifiers
}  // namespace theory
}  // namespace CVC4
