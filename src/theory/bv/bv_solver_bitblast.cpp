/******************************************************************************
 * Top contributors (to current version):
 *   Mathias Preiner, Andrew Reynolds, Aina Niemetz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2025 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Bit-blasting solver that supports multiple SAT backends.
 */

#include "theory/bv/bv_solver_bitblast.h"

#include "options/bv_options.h"
#include "prop/cnf_stream.h"
#include "prop/sat_solver.h"
#include "prop/sat_solver_factory.h"
#include "theory/bv/theory_bv.h"
#include "theory/bv/theory_bv_utils.h"
#include "theory/bv/bitblast/node_bitblaster.h"
#include "theory/theory_model.h"

namespace cvc5::internal {
namespace theory {
namespace bv {

/**
 * Notifies the BV solver when assertions were reset.
 *
 * This class is notified after every user-context pop and maintains a flag
 * that indicates whether assertions have been reset. If the user-context level
 * reaches level 0 it means that the assertions were reset.
 */
class NotifyResetAssertions : public context::ContextNotifyObj
{
 public:
  NotifyResetAssertions(context::Context* c)
      : context::ContextNotifyObj(c, false),
        d_context(c),
        d_doneResetAssertions(false)
  {
  }

  bool doneResetAssertions() const { return d_doneResetAssertions; }

  void reset() { d_doneResetAssertions = false; }

 protected:
  void contextNotifyPop() override
  {
    // If the user-context level reaches 0 it means that reset-assertions was
    // called.
    if (d_context->getLevel() == 0)
    {
      d_doneResetAssertions = true;
    }
  }

 private:
  /** The user-context. */
  context::Context* d_context;

  /** Flag to notify whether reset assertions was called. */
  bool d_doneResetAssertions;
};

/**
 * Bit-blasting registrar.
 *
 * The CnfStream calls preRegister() if it encounters a theory atom.
 * This registrar bit-blasts given atom and remembers which bit-vector atoms
 * were bit-blasted.
 *
 * This registrar is needed when --bitblast=eager is enabled.
 */
class BBRegistrar : public prop::Registrar
{
 public:
  explicit BBRegistrar() = default;

  void notifySatLiteral(Node n) override
  {
    if (d_registeredAtoms.find(n) != d_registeredAtoms.end())
    {
      return;
    }
    /* We are only interested in bit-vector atoms. */
    if ((n.getKind() == Kind::EQUAL && n[0].getType().isBitVector())
        || n.getKind() == Kind::BITVECTOR_ULT
        || n.getKind() == Kind::BITVECTOR_ULE
        || n.getKind() == Kind::BITVECTOR_SLT
        || n.getKind() == Kind::BITVECTOR_SLE)
    {
      d_registeredAtoms.insert(n);
    }
  }

  std::unordered_set<TNode>& getRegisteredAtoms() { return d_registeredAtoms; }

 private:
  /** Stores bit-vector atoms encountered on preRegister(). */
  std::unordered_set<TNode> d_registeredAtoms;
};

class BitBlasterWrapper : protected EnvObj
{
 public:
  explicit BitBlasterWrapper(Env& env)
    : EnvObj(env),
      d_bitblaster(new NodeBitblaster(env)),
      d_bbRegistrar(new BBRegistrar()),
      d_nullContext(new context::Context()),
      d_assertions(context()),
      d_factLiteralCache(context()),
      d_literalFactCache(context())
  {
    switch (options().bv.bvSatSolver)
    {
      case options::BvSatSolverMode::CRYPTOMINISAT:
        d_satSolver.reset(prop::SatSolverFactory::createCryptoMinisat(
            statisticsRegistry(),
            d_env.getResourceManager(),
            "theory::bv::BVSolverBitblast::"));
        break;
      default:
        d_satSolver.reset(prop::SatSolverFactory::createCadical(
            d_env,
            statisticsRegistry(),
            d_env.getResourceManager(),
            "theory::bv::BVSolverBitblast::"));
    }
    d_cnfStream.reset(new prop::CnfStream(d_env,
                                          d_satSolver.get(),
                                          d_bbRegistrar.get(),
                                          d_nullContext.get(),
                                          prop::FormulaLitPolicy::INTERNAL,
                                          "theory::bv::BVSolverBitblast"));
  }

  ~BitBlasterWrapper() override = default;

 private:
  /** Bit-blaster used to bit-blast atoms/terms. */
  std::unique_ptr<NodeBitblaster> d_bitblaster;

  /** Used for initializing `d_cnfStream`. */
  std::unique_ptr<BBRegistrar> d_bbRegistrar;
  std::unique_ptr<context::Context> d_nullContext;

  /** SAT solver back end. */
  std::unique_ptr<prop::SatSolver> d_satSolver;
  /** CNF stream. */
  std::unique_ptr<prop::CnfStream> d_cnfStream;

  /** Stores the current input assertions. */
  context::CDHashSet<Node> d_assertions;

  /** Stores the SatLiteral for a given assumption.
   *  Reverse map of `d_literalFactCache`. */
  context::CDHashMap<Node, prop::SatLiteral> d_factLiteralCache;

  /** Stores the Fact for a SatLiteral of an assumption.
   *  Reverse map of `d_factLiteralCache`. */
  context::CDHashMap<prop::SatLiteral, Node, prop::SatLiteralHashFunction>
      d_literalFactCache;

  void processRegisteredAtoms()
  {
    /* convertAndAssert() does not make the connection between the bit-vector
     * atom and its bit-blasted form (it only calls preRegister() from the
     * registrar). Thus, we add the equalities now. */
    auto& registeredAtoms = d_bbRegistrar->getRegisteredAtoms();
    for (auto atom : registeredAtoms)
    {
      d_bitblaster->bbAtom(atom);
      Node bb_atom = d_bitblaster->getBBAtom(atom);
      d_cnfStream->convertAndAssert(atom.eqNode(bb_atom), false, false);
    }
    // Clear cache since we only need to do this once per bit-blasted atom.
    registeredAtoms.clear();
  }

public:
  bool hasAssertion(const TNode fact) const
  {
    return d_assertions.contains(fact);
  }

  bool hasAssumption(const TNode fact) const
  {
    return d_factLiteralCache.find(fact) != d_factLiteralCache.end();
  }

  bool hasAssumption(const prop::SatLiteral lit) const
  {
    return d_literalFactCache.find(lit) != d_literalFactCache.end();
  }

  void assertAtom(TNode fact)
  {
    if (hasAssertion(fact))
    {
      return;
    }
    if (fact.getKind() == Kind::BITVECTOR_EAGER_ATOM)
    {
      // add the whole atom to the cnf stream ...
      d_cnfStream->convertAndAssert(fact[0], false, false);
      // and bitblast all assertions individually
      processRegisteredAtoms();
    }
    else
    {
      // bitblast the atom
      d_bitblaster->bbAtom(fact);
      Node bb_fact = d_bitblaster->getBBAtom(fact);
      // and assert it
      d_cnfStream->convertAndAssert(bb_fact, false, false);
    }
    d_assertions.insert(fact);
  }

  void assumeAtom(TNode atom)
  {
    if (hasAssumption(atom))
    {
      return;
    }
    prop::SatLiteral lit;
    if (atom.getKind() == Kind::BITVECTOR_EAGER_ATOM)
    {
      d_cnfStream->ensureLiteral(atom[0]);
      processRegisteredAtoms();
      lit = d_cnfStream->getLiteral(atom[0]);
    }
    else
    {
      d_bitblaster->bbAtom(atom);
      Node bb_fact = d_bitblaster->getBBAtom(atom);
      d_cnfStream->ensureLiteral(bb_fact);
      lit = d_cnfStream->getLiteral(bb_fact);
    }
    d_factLiteralCache[atom] = lit;
    d_literalFactCache[lit] = atom;
  }

  /** Runs the SAT solver. There are three result options:
   *  SAT: `true` is returned, `conflict` remains unchanged.
   *  UNSAT: `false` is returned and conflict contains a conflict core.
   *  UNKNOWN: `false` is returned and conflict remains unchanged. */
  bool solve(std::vector<Node>& conflict)
  {
    std::vector<prop::SatLiteral> assumptions;
    for (const auto& kv : d_literalFactCache)
    {
      assumptions.push_back(kv.first);
    }
    prop::SatValue val = d_satSolver->solve(assumptions);
    if (val == prop::SatValue::SAT_VALUE_FALSE)
    {
      std::vector<prop::SatLiteral> unsat_assumptions;
      d_satSolver->getUnsatAssumptions(unsat_assumptions);
      if (!unsat_assumptions.empty())
      {
        // Unsat assumptions produce conflict.
        for (const prop::SatLiteral& lit : unsat_assumptions)
        {
          conflict.push_back(d_literalFactCache[lit]);
          Trace("bv-bitblast")
              << "unsat assumption (" << lit << "): " << conflict.back() << std::endl;
        }
      }
      else
      {
        // Input assertions produce conflict.
        for (const auto& n : d_assertions)
        {
          conflict.push_back(n);
        }
      }
      Assert(!conflict.empty());
    }
    return val == prop::SatValue::SAT_VALUE_TRUE;
  }

  bool setPropagateOnly()
  {
    return d_satSolver->setPropagateOnly();
  }

  void collectVariables(std::set<Node>& variables) const
  {
    // collect bit-blasted variables
    d_bitblaster->collectVariables(variables);

    // and Boolean variables inside eager nodes
    std::vector<TNode> tmp;
    d_cnfStream->getBooleanVariables(tmp);
    variables.insert(tmp.begin(), tmp.end());
  }

  bool isVariable(TNode node) const
  {
    // either it is a bitblasted variable or a boolean variable inside an eager atom
    return d_bitblaster->isVariable(node) || d_cnfStream->hasLiteral(node);
  }

  /** Gets the value of `node` */
  Node getValue(TNode node, bool initialize) const
  {
    NodeManager* nm = node.getNodeManager();
    // it's a boolean variable
    if (d_cnfStream->hasLiteral(node))
    {
      Assert(node.getType().isBoolean());
      prop::SatLiteral bit = d_cnfStream->getLiteral(node);
      prop::SatValue value = d_satSolver->modelValue(bit);
      Assert(value != prop::SAT_VALUE_UNKNOWN);
      return nm->mkConst(value == prop::SAT_VALUE_TRUE);
    }

    // it's a BV variable
    if (d_bitblaster->hasBBTerm(node))
    {
      Assert(node.getType().isBitVector());
      std::vector<Node> bits;
      d_bitblaster->getBBTerm(node, bits);
      Integer value(0);
      const Integer one(1), zero(0);
      for (size_t i = 0, size = bits.size(), j = size - 1; i < size; ++i, --j)
      {
        Integer bit;
        if (d_cnfStream->hasLiteral(bits[j]))
        {
          prop::SatLiteral lit = d_cnfStream->getLiteral(bits[j]);
          prop::SatValue val = d_satSolver->modelValue(lit);
          bit = val == prop::SatValue::SAT_VALUE_TRUE ? one : zero;
        }
        else
        {
          if (!initialize) return Node();
          bit = zero;
        }
        value = value * 2 + bit;
      }
      return utils::mkConst(nm, bits.size(), value);
    }

    // it's neither
    Assert(node.getType().isBitVector() || node.getType().isBoolean());
    if (initialize)
    {
      return node.getType().isBitVector()
                 ? utils::mkConst(nm, utils::getSize(node), 0u)
                 : nm->mkConst(false);
    }
    return Node();
  }
};

BVSolverBitblast::BVSolverBitblast(Env& env,
                                   TheoryState& state,
                                   TheoryInferenceManager& inferMgr)
    : BVSolver(env, state, inferMgr),
      d_bitblaster(new BitBlasterWrapper(env)),
      d_bbFacts(context()),
      d_bbInputFacts(context()),
      d_resetNotify(new NotifyResetAssertions(userContext()))
{
  if (env.isTheoryProofProducing())
  {
    d_epg.reset(new EagerProofGenerator(env, userContext(), ""));
    d_bvProofChecker.reset(new BVProofRuleChecker(nodeManager()));
    d_bvProofChecker->registerTo(env.getProofNodeManager()->getChecker());
  }
}

bool BVSolverBitblast::needsEqualityEngine(EeSetupInfo& esi)
{
  // we always need the equality engine if sharing is enabled for processing
  // equality engine and shared terms
  return logicInfo().isSharingEnabled() || options().bv.bvEqEngine;
}

void BVSolverBitblast::postCheck(Theory::Effort level)
{
  if (level != Theory::Effort::EFFORT_FULL)
  {
    /* Do bit-level propagation only if the SAT solver supports it. */
    if (!options().bv.bitvectorPropagate || !d_bitblaster->setPropagateOnly())
    {
      return;
    }
  }

  // If we permanently added assertions to the SAT solver and the assertions
  // were reset, we have to reset the SAT solver and the CNF stream.
  if (options().bv.bvAssertInput && d_resetNotify->doneResetAssertions())
  {
    d_bitblaster.reset(new BitBlasterWrapper(d_env));
    d_resetNotify->reset();
  }

  /* Process input assertions bit-blast queue. */
  while (!d_bbInputFacts.empty())
  {
    d_bitblaster->assertAtom(d_bbInputFacts.front());
    d_bbInputFacts.pop();
  }

  /* Process bit-blast queue and store SAT literals. */
  while (!d_bbFacts.empty())
  {
    d_bitblaster->assumeAtom(d_bbFacts.front());
    d_bbFacts.pop();
  }

  std::vector<Node> core;
  bool sat = d_bitblaster->solve(core);
  if (!sat)
  {
    // we don't expect the SAT solver to report unknown, right?
    Assert(!core.empty());
    const Node conflict = nodeManager()->mkAnd(core);
    TrustNode conflict_trust;
    if (d_epg != nullptr)
    {
      conflict_trust = d_epg->mkTrustNodeTrusted(
          conflict, TrustId::BV_BITBLAST_CONFLICT, {}, {}, true);
    }
    else
    {
      conflict_trust = TrustNode::mkTrustConflict(conflict, nullptr);
    }
    d_im.trustedConflict(conflict_trust, InferenceId::BV_BITBLAST_CONFLICT);
  }
}

bool BVSolverBitblast::preNotifyFact(
    TNode atom, bool pol, TNode fact, bool isPrereg, bool isInternal)
{
  Valuation& val = d_state.getValuation();

  /**
   * Check whether `fact` is an input assertion on user-level 0.
   *
   * If this is the case we can assert `fact` to the SAT solver instead of
   * using assumptions.
   */
  if (options().bv.bvAssertInput && val.isFixed(fact))
  {
    Assert(!val.isDecision(fact));
    d_bbInputFacts.push_back(fact);
  }
  else
  {
    d_bbFacts.push_back(fact);
  }
  
  // Return false to enable equality engine reasoning in Theory, which is
  // available if we are using the equality engine.
  return !logicInfo().isSharingEnabled() && !options().bv.bvEqEngine;
}

TrustNode BVSolverBitblast::explain(TNode n)
{
  Trace("bv-bitblast") << "explain called on " << n << std::endl;
  return d_im.explainLit(n);
}

void BVSolverBitblast::computeRelevantTerms(std::set<Node>& termSet)
{
  /* BITVECTOR_EAGER_ATOM wraps input assertions that may also contain
   * equalities. As a result, these equalities are not handled by the equality
   * engine and terms below these equalities do not appear in `termSet`.
   * We need to make sure that we compute model values for all relevant terms
   * in BitblastMode::EAGER and therefore add all variables from the
   * bit-blaster to `termSet`.
   */
  if (options().bv.bitblastMode == options::BitblastMode::EAGER)
  {
    d_bitblaster->collectVariables(termSet);
  }
}

bool BVSolverBitblast::collectModelValues(TheoryModel* m,
                                          const std::set<Node>& termSet)
{
  for (const auto& term : termSet)
  {
    if (!d_bitblaster->isVariable(term))
    {
      continue;
    }
    Node value = d_bitblaster->getValue(term, true);
    Assert(value.isConst());
    if (!m->assertEquality(term, value, true))
    {
      return false;
    }
  }

  return true;
}

Node BVSolverBitblast::getValue(TNode node, bool initialize)
{
  if (node.isConst())
  {
    return node;
  }

  return d_bitblaster->getValue(node, initialize);
}

}  // namespace bv
}  // namespace theory
}  // namespace cvc5::internal
