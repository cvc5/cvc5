/*********************                                                        */
/*! \file lazy_bitblaster.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Liana Hadarean, Aina Niemetz, Mathias Preiner
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Bitblaster for the lazy bv solver.
 **
 ** Bitblaster for the lazy bv solver.
 **/

#include "theory/bv/bitblast/lazy_bitblaster.h"

#include "cvc4_private.h"
#include "options/bv_options.h"
#include "prop/cnf_stream.h"
#include "prop/sat_solver.h"
#include "prop/sat_solver_factory.h"
#include "smt/smt_engine.h"
#include "smt/smt_statistics_registry.h"
#include "theory/bv/abstraction.h"
#include "theory/bv/bv_solver_lazy.h"
#include "theory/bv/theory_bv.h"
#include "theory/bv/theory_bv_utils.h"
#include "theory/rewriter.h"
#include "theory/theory_model.h"

namespace CVC4 {
namespace theory {
namespace bv {

namespace {

/* Determine the number of uncached nodes that a given node consists of.  */
uint64_t numNodes(TNode node, utils::NodeSet& seen)
{
  std::vector<TNode> stack;
  uint64_t res = 0;

  stack.push_back(node);
  while (!stack.empty())
  {
    Node n = stack.back();
    stack.pop_back();

    if (seen.find(n) != seen.end()) continue;

    res += 1;
    seen.insert(n);
    stack.insert(stack.end(), n.begin(), n.end());
  }
  return res;
}
}

TLazyBitblaster::TLazyBitblaster(context::Context* c,
                                 bv::BVSolverLazy* bv,
                                 const std::string name,
                                 bool emptyNotify)
    : TBitblaster<Node>(),
      d_bv(bv),
      d_ctx(c),
      d_nullRegistrar(new prop::NullRegistrar()),
      d_assertedAtoms(new (true) context::CDList<prop::SatLiteral>(c)),
      d_explanations(new (true) ExplanationMap(c)),
      d_variables(),
      d_bbAtoms(),
      d_abstraction(NULL),
      d_emptyNotify(emptyNotify),
      d_fullModelAssertionLevel(c, 0),
      d_name(name),
      d_statistics(name)
{
  d_satSolver.reset(
      prop::SatSolverFactory::createMinisat(c, smtStatisticsRegistry(), name));

  ResourceManager* rm = smt::currentResourceManager();
  d_cnfStream.reset(new prop::TseitinCnfStream(d_satSolver.get(),
                                               d_nullRegistrar.get(),
                                               d_nullContext.get(),
                                               nullptr,
                                               rm,
                                               false,
                                               "LazyBitblaster"));

  d_satSolverNotify.reset(
      d_emptyNotify
          ? (prop::BVSatSolverNotify*)new MinisatEmptyNotify()
          : (prop::BVSatSolverNotify*)new MinisatNotify(
                d_cnfStream.get(), bv, this));

  d_satSolver->setNotify(d_satSolverNotify.get());
}

void TLazyBitblaster::setAbstraction(AbstractionModule* abs) {
  d_abstraction = abs;
}

TLazyBitblaster::~TLazyBitblaster()
{
  d_assertedAtoms->deleteSelf();
  d_explanations->deleteSelf();
}


/**
 * Bitblasts the atom, assigns it a marker literal, adding it to the SAT solver
 * NOTE: duplicate clauses are not detected because of marker literal
 * @param node the atom to be bitblasted
 *
 */
void TLazyBitblaster::bbAtom(TNode node)
{
  NodeManager* nm = NodeManager::currentNM();
  node = node.getKind() == kind::NOT ? node[0] : node;

  if (hasBBAtom(node))
  {
    return;
  }

  // make sure it is marked as an atom
  addAtom(node);

  Debug("bitvector-bitblast") << "Bitblasting node " << node << "\n";
  ++d_statistics.d_numAtoms;

  /// if we are using bit-vector abstraction bit-blast the original
  /// interpretation
  if (options::bvAbstraction() && d_abstraction != NULL
      && d_abstraction->isAbstraction(node))
  {
    // node must be of the form P(args) = bv1
    Node expansion = Rewriter::rewrite(d_abstraction->getInterpretation(node));

    Node atom_bb;
    if (expansion.getKind() == kind::CONST_BOOLEAN)
    {
      atom_bb = expansion;
    }
    else
    {
      Assert(expansion.getKind() == kind::AND);
      std::vector<Node> atoms;
      for (unsigned i = 0; i < expansion.getNumChildren(); ++i)
      {
        Node normalized_i = Rewriter::rewrite(expansion[i]);
        Node atom_i =
            normalized_i.getKind() != kind::CONST_BOOLEAN
                ? Rewriter::rewrite(d_atomBBStrategies[normalized_i.getKind()](
                      normalized_i, this))
                : normalized_i;
        atoms.push_back(atom_i);
      }
      atom_bb = utils::mkAnd(atoms);
    }
    Assert(!atom_bb.isNull());
    Node atom_definition = nm->mkNode(kind::EQUAL, node, atom_bb);
    storeBBAtom(node, atom_bb);
    d_cnfStream->convertAndAssert(atom_definition, false, false);
    return;
  }

  // the bitblasted definition of the atom
  Node normalized = Rewriter::rewrite(node);
  Node atom_bb =
      normalized.getKind() != kind::CONST_BOOLEAN
          ? d_atomBBStrategies[normalized.getKind()](normalized, this)
          : normalized;

  atom_bb = Rewriter::rewrite(atom_bb);

  // asserting that the atom is true iff the definition holds
  Node atom_definition = nm->mkNode(kind::EQUAL, node, atom_bb);
  storeBBAtom(node, atom_bb);
  d_cnfStream->convertAndAssert(atom_definition, false, false);
}

void TLazyBitblaster::storeBBAtom(TNode atom, Node atom_bb) {
  d_bbAtoms.insert(atom);
}

void TLazyBitblaster::storeBBTerm(TNode node, const Bits& bits) {
  d_termCache.insert(std::make_pair(node, bits));
}


bool TLazyBitblaster::hasBBAtom(TNode atom) const {
  return d_bbAtoms.find(atom) != d_bbAtoms.end();
}


void TLazyBitblaster::makeVariable(TNode var, Bits& bits) {
  Assert(bits.size() == 0);
  for (unsigned i = 0; i < utils::getSize(var); ++i) {
    bits.push_back(utils::mkBitOf(var, i));
  }
  d_variables.insert(var);
}

uint64_t TLazyBitblaster::computeAtomWeight(TNode node, NodeSet& seen)
{
  node = node.getKind() == kind::NOT ? node[0] : node;
  if (!utils::isBitblastAtom(node)) { return 0; }
  Node atom_bb =
      Rewriter::rewrite(d_atomBBStrategies[node.getKind()](node, this));
  uint64_t size = numNodes(atom_bb, seen);
  return size;
}

// cnf conversion ensures the atom represents itself
Node TLazyBitblaster::getBBAtom(TNode node) const {
  return node;
}

void TLazyBitblaster::bbTerm(TNode node, Bits& bits) {

  if (hasBBTerm(node)) {
    getBBTerm(node, bits);
    return;
  }
  Assert(node.getType().isBitVector());

  d_bv->spendResource(ResourceManager::Resource::BitblastStep);
  Debug("bitvector-bitblast") << "Bitblasting term " << node <<"\n";
  ++d_statistics.d_numTerms;

  d_termBBStrategies[node.getKind()] (node, bits,this);

  Assert(bits.size() == utils::getSize(node));

  storeBBTerm(node, bits);
}
/// Public methods

void TLazyBitblaster::addAtom(TNode atom) {
  d_cnfStream->ensureLiteral(atom);
  prop::SatLiteral lit = d_cnfStream->getLiteral(atom);
  d_satSolver->addMarkerLiteral(lit);
}

void TLazyBitblaster::explain(TNode atom, std::vector<TNode>& explanation) {
  prop::SatLiteral lit = d_cnfStream->getLiteral(atom);

  ++(d_statistics.d_numExplainedPropagations);
  if (options::bvEagerExplanations()) {
    Assert(d_explanations->find(lit) != d_explanations->end());
    const std::vector<prop::SatLiteral>& literal_explanation = (*d_explanations)[lit].get();
    for (unsigned i = 0; i < literal_explanation.size(); ++i) {
      explanation.push_back(d_cnfStream->getNode(literal_explanation[i]));
    }
    return;
  }

  std::vector<prop::SatLiteral> literal_explanation;
  d_satSolver->explain(lit, literal_explanation);
  for (unsigned i = 0; i < literal_explanation.size(); ++i) {
    explanation.push_back(d_cnfStream->getNode(literal_explanation[i]));
  }
}


/*
 * Asserts the clauses corresponding to the atom to the Sat Solver
 * by turning on the marker literal (i.e. setting it to false)
 * @param node the atom to be asserted
 *
 */

bool TLazyBitblaster::propagate() {
  return d_satSolver->propagate() == prop::SAT_VALUE_TRUE;
}

bool TLazyBitblaster::assertToSat(TNode lit, bool propagate) {
  // strip the not
  TNode atom;
  if (lit.getKind() == kind::NOT) {
    atom = lit[0];
  } else {
    atom = lit;
  }
  Assert(utils::isBitblastAtom(atom));

  Assert(hasBBAtom(atom));

  prop::SatLiteral markerLit = d_cnfStream->getLiteral(atom);

  if(lit.getKind() == kind::NOT) {
    markerLit = ~markerLit;
  }

  Debug("bitvector-bb")
      << "BVSolverLazy::TLazyBitblaster::assertToSat asserting node: " << atom
      << "\n";
  Debug("bitvector-bb")
      << "BVSolverLazy::TLazyBitblaster::assertToSat with literal:   "
      << markerLit << "\n";

  prop::SatValue ret = d_satSolver->assertAssumption(markerLit, propagate);

  d_assertedAtoms->push_back(markerLit);

  return ret == prop::SAT_VALUE_TRUE || ret == prop::SAT_VALUE_UNKNOWN;
}

/**
 * Calls the solve method for the Sat Solver.
 * passing it the marker literals to be asserted
 *
 * @return true for sat, and false for unsat
 */

bool TLazyBitblaster::solve() {
  if (Trace.isOn("bitvector")) {
    Trace("bitvector") << "TLazyBitblaster::solve() asserted atoms ";
    context::CDList<prop::SatLiteral>::const_iterator it = d_assertedAtoms->begin();
    for (; it != d_assertedAtoms->end(); ++it) {
      Trace("bitvector") << "     " << d_cnfStream->getNode(*it) << "\n";
    }
  }
  Debug("bitvector") << "TLazyBitblaster::solve() asserted atoms " << d_assertedAtoms->size() <<"\n";
  d_fullModelAssertionLevel.set(d_bv->numAssertions());
  return prop::SAT_VALUE_TRUE == d_satSolver->solve();
}

prop::SatValue TLazyBitblaster::solveWithBudget(unsigned long budget) {
  if (Trace.isOn("bitvector")) {
    Trace("bitvector") << "TLazyBitblaster::solveWithBudget() asserted atoms ";
    context::CDList<prop::SatLiteral>::const_iterator it = d_assertedAtoms->begin();
    for (; it != d_assertedAtoms->end(); ++it) {
      Trace("bitvector") << "     " << d_cnfStream->getNode(*it) << "\n";
    }
  }
  Debug("bitvector") << "TLazyBitblaster::solveWithBudget() asserted atoms " << d_assertedAtoms->size() <<"\n";
  return d_satSolver->solve(budget);
}

void TLazyBitblaster::getConflict(std::vector<TNode>& conflict)
{
  NodeManager* nm = NodeManager::currentNM();
  prop::SatClause conflictClause;
  d_satSolver->getUnsatCore(conflictClause);

  for (unsigned i = 0; i < conflictClause.size(); i++)
  {
    prop::SatLiteral lit = conflictClause[i];
    TNode atom = d_cnfStream->getNode(lit);
    Node not_atom;
    if (atom.getKind() == kind::NOT)
    {
      not_atom = atom[0];
    }
    else
    {
      not_atom = nm->mkNode(kind::NOT, atom);
    }
    conflict.push_back(not_atom);
  }
}

TLazyBitblaster::Statistics::Statistics(const std::string& prefix) :
  d_numTermClauses(prefix + "::NumTermSatClauses", 0),
  d_numAtomClauses(prefix + "::NumAtomSatClauses", 0),
  d_numTerms(prefix + "::NumBitblastedTerms", 0),
  d_numAtoms(prefix + "::NumBitblastedAtoms", 0),
  d_numExplainedPropagations(prefix + "::NumExplainedPropagations", 0),
  d_numBitblastingPropagations(prefix + "::NumBitblastingPropagations", 0),
  d_bitblastTimer(prefix + "::BitblastTimer")
{
  smtStatisticsRegistry()->registerStat(&d_numTermClauses);
  smtStatisticsRegistry()->registerStat(&d_numAtomClauses);
  smtStatisticsRegistry()->registerStat(&d_numTerms);
  smtStatisticsRegistry()->registerStat(&d_numAtoms);
  smtStatisticsRegistry()->registerStat(&d_numExplainedPropagations);
  smtStatisticsRegistry()->registerStat(&d_numBitblastingPropagations);
  smtStatisticsRegistry()->registerStat(&d_bitblastTimer);
}


TLazyBitblaster::Statistics::~Statistics() {
  smtStatisticsRegistry()->unregisterStat(&d_numTermClauses);
  smtStatisticsRegistry()->unregisterStat(&d_numAtomClauses);
  smtStatisticsRegistry()->unregisterStat(&d_numTerms);
  smtStatisticsRegistry()->unregisterStat(&d_numAtoms);
  smtStatisticsRegistry()->unregisterStat(&d_numExplainedPropagations);
  smtStatisticsRegistry()->unregisterStat(&d_numBitblastingPropagations);
  smtStatisticsRegistry()->unregisterStat(&d_bitblastTimer);
}

bool TLazyBitblaster::MinisatNotify::notify(prop::SatLiteral lit) {
  if(options::bvEagerExplanations()) {
    // compute explanation
    if (d_lazyBB->d_explanations->find(lit) == d_lazyBB->d_explanations->end()) {
      std::vector<prop::SatLiteral> literal_explanation;
      d_lazyBB->d_satSolver->explain(lit, literal_explanation);
      d_lazyBB->d_explanations->insert(lit, literal_explanation);
    } else {
      // we propagated it at a lower level
      return true;
    }
  }
  ++(d_lazyBB->d_statistics.d_numBitblastingPropagations);
  TNode atom = d_cnf->getNode(lit);
  return d_bv->storePropagation(atom, SUB_BITBLAST);
}

void TLazyBitblaster::MinisatNotify::notify(prop::SatClause& clause) {
  if (clause.size() > 1) {
    NodeBuilder<> lemmab(kind::OR);
    for (unsigned i = 0; i < clause.size(); ++ i) {
      lemmab << d_cnf->getNode(clause[i]);
    }
    Node lemma = lemmab;
    d_bv->d_inferManager.lemma(lemma);
  } else {
    d_bv->d_inferManager.lemma(d_cnf->getNode(clause[0]));
  }
}

void TLazyBitblaster::MinisatNotify::spendResource(ResourceManager::Resource r)
{
  d_bv->spendResource(r);
}

void TLazyBitblaster::MinisatNotify::safePoint(ResourceManager::Resource r)
{
  d_bv->d_inferManager.safePoint(r);
}

EqualityStatus TLazyBitblaster::getEqualityStatus(TNode a, TNode b)
{
  int numAssertions = d_bv->numAssertions();
  bool has_full_model =
      numAssertions != 0 && d_fullModelAssertionLevel.get() == numAssertions;

  Debug("bv-equality-status")
      << "TLazyBitblaster::getEqualityStatus " << a << " = " << b << "\n";
  Debug("bv-equality-status")
      << "BVSatSolver has full model? " << has_full_model << "\n";

  // First check if it trivially rewrites to false/true
  Node a_eq_b =
      Rewriter::rewrite(NodeManager::currentNM()->mkNode(kind::EQUAL, a, b));

  if (a_eq_b == utils::mkFalse()) return theory::EQUALITY_FALSE;
  if (a_eq_b == utils::mkTrue()) return theory::EQUALITY_TRUE;

  if (!has_full_model)
  {
    return theory::EQUALITY_UNKNOWN;
  }

  // Check if cache is valid (invalidated in check and pops)
  if (d_bv->d_invalidateModelCache.get())
  {
    invalidateModelCache();
  }
  d_bv->d_invalidateModelCache.set(false);

  Node a_value = getTermModel(a, true);
  Node b_value = getTermModel(b, true);

  Assert(a_value.isConst() && b_value.isConst());

  if (a_value == b_value)
  {
    Debug("bv-equality-status") << "theory::EQUALITY_TRUE_IN_MODEL\n";
    return theory::EQUALITY_TRUE_IN_MODEL;
  }
  Debug("bv-equality-status") << "theory::EQUALITY_FALSE_IN_MODEL\n";
  return theory::EQUALITY_FALSE_IN_MODEL;
}

bool TLazyBitblaster::isSharedTerm(TNode node) {
  return d_bv->d_sharedTermsSet.find(node) != d_bv->d_sharedTermsSet.end();
}

bool TLazyBitblaster::hasValue(TNode a) {
  Assert(hasBBTerm(a));
  Bits bits;
  getBBTerm(a, bits);
  for (int i = bits.size() -1; i >= 0; --i) {
    prop::SatValue bit_value;
    if (d_cnfStream->hasLiteral(bits[i])) {
      prop::SatLiteral bit = d_cnfStream->getLiteral(bits[i]);
      bit_value = d_satSolver->value(bit);
      if (bit_value ==  prop::SAT_VALUE_UNKNOWN)
        return false;
    } else {
      return false;
    }
  }
  return true;
}
/**
 * Returns the value a is currently assigned to in the SAT solver
 * or null if the value is completely unassigned.
 *
 * @param a
 * @param fullModel whether to create a "full model," i.e., add
 * constants to equivalence classes that don't already have them
 *
 * @return
 */
Node TLazyBitblaster::getModelFromSatSolver(TNode a, bool fullModel) {
  if (!hasBBTerm(a)) {
    return fullModel? utils::mkConst(utils::getSize(a), 0u) : Node();
  }

  Bits bits;
  getBBTerm(a, bits);
  Integer value(0);
  for (int i = bits.size() -1; i >= 0; --i) {
    prop::SatValue bit_value;
    if (d_cnfStream->hasLiteral(bits[i])) {
      prop::SatLiteral bit = d_cnfStream->getLiteral(bits[i]);
      bit_value = d_satSolver->value(bit);
      Assert(bit_value != prop::SAT_VALUE_UNKNOWN);
    } else {
      if (!fullModel) return Node();
      // unconstrained bits default to false
      bit_value = prop::SAT_VALUE_FALSE;
    }
    Integer bit_int = bit_value == prop::SAT_VALUE_TRUE ? Integer(1) : Integer(0);
    value = value * 2 + bit_int;
  }
  return utils::mkConst(bits.size(), value);
}

bool TLazyBitblaster::collectModelValues(TheoryModel* m,
                                         const std::set<Node>& termSet)
{
  for (std::set<Node>::const_iterator it = termSet.begin(); it != termSet.end(); ++it) {
    TNode var = *it;
    // not actually a leaf of the bit-vector theory
    if (d_variables.find(var) == d_variables.end())
      continue;

    Assert(Theory::theoryOf(var) == theory::THEORY_BV || isSharedTerm(var));
    // only shared terms could not have been bit-blasted
    Assert(hasBBTerm(var) || isSharedTerm(var));

    Node const_value = getModelFromSatSolver(var, true);
    Assert(const_value.isNull() || const_value.isConst());
    if(const_value != Node()) {
      Debug("bitvector-model")
          << "TLazyBitblaster::collectModelValues (assert (= " << var << " "
          << const_value << "))\n";
      if (!m->assertEquality(var, const_value, true))
      {
        return false;
      }
    }
  }
  return true;
}

void TLazyBitblaster::clearSolver() {
  Assert(d_ctx->getLevel() == 0);
  d_assertedAtoms->deleteSelf();
  d_assertedAtoms = new(true) context::CDList<prop::SatLiteral>(d_ctx);
  d_explanations->deleteSelf();
  d_explanations = new(true) ExplanationMap(d_ctx);
  d_bbAtoms.clear();
  d_variables.clear();
  d_termCache.clear();

  invalidateModelCache();
  // recreate sat solver
  d_satSolver.reset(
      prop::SatSolverFactory::createMinisat(d_ctx, smtStatisticsRegistry()));
  ResourceManager* rm = smt::currentResourceManager();
  d_cnfStream.reset(new prop::TseitinCnfStream(d_satSolver.get(),
                                               d_nullRegistrar.get(),
                                               d_nullContext.get(),
                                               nullptr,
                                               rm));
  d_satSolverNotify.reset(
      d_emptyNotify
          ? (prop::BVSatSolverNotify*)new MinisatEmptyNotify()
          : (prop::BVSatSolverNotify*)new MinisatNotify(
                d_cnfStream.get(), d_bv, this));
  d_satSolver->setNotify(d_satSolverNotify.get());
}

}  // namespace bv
}  // namespace theory
}  // namespace CVC4
