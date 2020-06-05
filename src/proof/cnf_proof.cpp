/*********************                                                        */
/*! \file cnf_proof.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Liana Hadarean, Andrew Reynolds, Alex Ozdemir
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief [[ Add one-line brief description here ]]
 **
 ** [[ Add lengthier description here ]]
 ** \todo document this file
 **/

#include "proof/cnf_proof.h"

#include "proof/clause_id.h"
#include "proof/proof_manager.h"
#include "proof/proof_utils.h"
#include "proof/theory_proof.h"
#include "prop/cnf_stream.h"
#include "prop/minisat/minisat.h"
#include "prop/sat_solver_types.h"

namespace CVC4 {

CnfProof::CnfProof(prop::CnfStream* stream,
                   context::Context* ctx,
                   const std::string& name)
  : d_cnfStream(stream)
  , d_clauseToAssertion(ctx)
  , d_assertionToProofRule(ctx)
  , d_currentAssertionStack()
  , d_currentDefinitionStack()
  , d_clauseToDefinition(ctx)
  , d_definitions()
  , d_cnfDeps()
  , d_name(name)
{
  // Setting the proof object for the CnfStream
  d_cnfStream->setProof(this);
}

CnfProof::~CnfProof() {}

bool CnfProof::isAssertion(Node node) {
  return d_assertionToProofRule.find(node) !=
         d_assertionToProofRule.end();
}

bool CnfProof::isDefinition(Node node) {
  return d_definitions.find(node) !=
         d_definitions.end();
}

ProofRule CnfProof::getProofRule(Node node) {
  Assert(isAssertion(node));
  NodeToProofRule::iterator it = d_assertionToProofRule.find(node);
  return (*it).second;
}

ProofRule CnfProof::getProofRule(ClauseId clause) {
  TNode assertion = getAssertionForClause(clause);
  return getProofRule(assertion);
}

Node CnfProof::getAssertionForClause(ClauseId clause) {
  ClauseIdToNode::const_iterator it = d_clauseToAssertion.find(clause);
  Assert(it != d_clauseToAssertion.end() && !(*it).second.isNull());
  return (*it).second;
}

Node CnfProof::getDefinitionForClause(ClauseId clause) {
  ClauseIdToNode::const_iterator it = d_clauseToDefinition.find(clause);
  Assert(it != d_clauseToDefinition.end());
  return (*it).second;
}

void CnfProof::registerConvertedClause(ClauseId clause, bool explanation) {
  Assert(clause != ClauseIdUndef && clause != ClauseIdError
         && clause != ClauseIdEmpty);

  // Explanations do not need a CNF conversion proof since they are in CNF
  // (they will only need a theory proof as they are theory valid)
  if (explanation) {
    Debug("proof:cnf") << "CnfProof::registerConvertedClause "
                       << clause << " explanation? " << explanation << std::endl;
    Assert(d_explanations.find(clause) == d_explanations.end());
    d_explanations.insert(clause);
    return;
  }

  Node current_assertion = getCurrentAssertion();
  Node current_expr = getCurrentDefinition();

  Debug("proof:cnf") << "CnfProof::registerConvertedClause "
                     << clause << " assertion = " << current_assertion
                     << clause << " definition = " << current_expr << std::endl;

  setClauseAssertion(clause, current_assertion);
  setClauseDefinition(clause, current_expr);
}

void CnfProof::registerTrueUnitClause(ClauseId clauseId)
{
  Node trueNode = NodeManager::currentNM()->mkConst<bool>(true);
  pushCurrentAssertion(trueNode);
  pushCurrentDefinition(trueNode);
  registerConvertedClause(clauseId);
  popCurrentAssertion();
  popCurrentDefinition();
  d_cnfStream->ensureLiteral(trueNode);
  d_trueUnitClause = clauseId;
}

void CnfProof::registerFalseUnitClause(ClauseId clauseId)
{
  Node falseNode = NodeManager::currentNM()->mkConst<bool>(false).notNode();
  pushCurrentAssertion(falseNode);
  pushCurrentDefinition(falseNode);
  registerConvertedClause(clauseId);
  popCurrentAssertion();
  popCurrentDefinition();
  d_cnfStream->ensureLiteral(falseNode);
  d_falseUnitClause = clauseId;
}

void CnfProof::setClauseAssertion(ClauseId clause, Node expr) {
  Debug("proof:cnf") << "CnfProof::setClauseAssertion "
                     << clause << " assertion " << expr << std::endl;
  // We can add the same clause from different assertions.  In this
  // case we keep the first assertion. For example asserting a /\ b
  // and then b /\ c where b is an atom, would assert b twice (note
  // that since b is top level, it is not cached by the CnfStream)
  //
  // Note: If the current assertion associated with the clause is null, we
  // update it because it means that it was previously added the clause without
  // associating it with an assertion.
  const auto& it = d_clauseToAssertion.find(clause);
  if (it != d_clauseToAssertion.end() && (*it).second != Node::null())
  {
    return;
  }

  d_clauseToAssertion.insert (clause, expr);
}

void CnfProof::setClauseDefinition(ClauseId clause, Node definition) {
  Debug("proof:cnf") << "CnfProof::setClauseDefinition "
                     << clause << " definition " << definition << std::endl;
  // We keep the first definition
  if (d_clauseToDefinition.find(clause) != d_clauseToDefinition.end())
    return;

  d_clauseToDefinition.insert(clause, definition);
  d_definitions.insert(definition);
}

void CnfProof::registerAssertion(Node assertion, ProofRule reason) {
  Debug("proof:cnf") << "CnfProof::registerAssertion "
                     << assertion << " reason " << reason << std::endl;
  // We can obtain the assertion from different reasons (e.g. if the
  // assertion is a lemma over shared terms both theories can generate
  // the same lemma) We only need to prove the lemma in one way, so we
  // keep the first reason.
  if (isAssertion(assertion)) {
    return;
  }
  d_assertionToProofRule.insert(assertion, reason);
}

LemmaProofRecipe CnfProof::getProofRecipe(const std::set<Node> &lemma) {
  Assert(d_lemmaToProofRecipe.find(lemma) != d_lemmaToProofRecipe.end());
  return d_lemmaToProofRecipe[lemma];
}

bool CnfProof::haveProofRecipe(const std::set<Node> &lemma) {
  return d_lemmaToProofRecipe.find(lemma) != d_lemmaToProofRecipe.end();
}

void CnfProof::setCnfDependence(Node from, Node to) {
  Debug("proof:cnf") << "CnfProof::setCnfDependence "
                     << "from " << from  << std::endl
                     << "     to " << to << std::endl;

  Assert(from != to);
  d_cnfDeps.insert(std::make_pair(from, to));
}

void CnfProof::pushCurrentAssertion(Node assertion) {
  Debug("proof:cnf") << "CnfProof::pushCurrentAssertion " << assertion
                     << std::endl;

  d_currentAssertionStack.push_back(assertion);

  Debug("proof:cnf") << "CnfProof::pushCurrentAssertion "
                     << "new stack size = " << d_currentAssertionStack.size()
                     << std::endl;
}

void CnfProof::popCurrentAssertion() {
  Assert(d_currentAssertionStack.size());

  Debug("proof:cnf") << "CnfProof::popCurrentAssertion "
                     << d_currentAssertionStack.back() << std::endl;

  d_currentAssertionStack.pop_back();

  Debug("proof:cnf") << "CnfProof::popCurrentAssertion "
                     << "new stack size = " << d_currentAssertionStack.size()
                     << std::endl;
}

Node CnfProof::getCurrentAssertion() {
  Assert(d_currentAssertionStack.size());
  return d_currentAssertionStack.back();
}

void CnfProof::setProofRecipe(LemmaProofRecipe* proofRecipe) {
  Assert(proofRecipe);
  Assert(proofRecipe->getNumSteps() > 0);
  d_lemmaToProofRecipe[proofRecipe->getBaseAssertions()] = *proofRecipe;
}

void CnfProof::pushCurrentDefinition(Node definition) {
  Debug("proof:cnf") << "CnfProof::pushCurrentDefinition "
                     << definition  << std::endl;

  d_currentDefinitionStack.push_back(definition);
}

void CnfProof::popCurrentDefinition() {
  Assert(d_currentDefinitionStack.size());

  Debug("proof:cnf") << "CnfProof::popCurrentDefinition "
                     << d_currentDefinitionStack.back() << std::endl;

  d_currentDefinitionStack.pop_back();
}

Node CnfProof::getCurrentDefinition() {
  Assert(d_currentDefinitionStack.size());
  return d_currentDefinitionStack.back();
}

Node CnfProof::getAtom(prop::SatVariable var) {
  prop::SatLiteral lit (var);
  Node node = d_cnfStream->getNode(lit);
  return node;
}

void CnfProof::collectAtoms(const prop::SatClause* clause,
                            std::set<Node>& atoms) {
  for (unsigned i = 0; i < clause->size(); ++i) {
    prop::SatLiteral lit = clause->operator[](i);
    prop::SatVariable var = lit.getSatVariable();
    TNode atom = getAtom(var);
    if (atoms.find(atom) == atoms.end()) {
      atoms.insert(atom);
    }
  }
}

prop::SatLiteral CnfProof::getLiteral(TNode atom) {
  return d_cnfStream->getLiteral(atom);
}

bool CnfProof::hasLiteral(TNode atom) {
  return d_cnfStream->hasLiteral(atom);
}

void CnfProof::ensureLiteral(TNode atom, bool noPreregistration) {
  d_cnfStream->ensureLiteral(atom, noPreregistration);
}

void CnfProof::collectAtomsForClauses(const IdToSatClause& clauses,
                                      std::set<Node>& atoms) {
  IdToSatClause::const_iterator it = clauses.begin();
  for (; it != clauses.end(); ++it) {
    const prop::SatClause* clause = it->second;
    collectAtoms(clause, atoms);
  }
}

void CnfProof::collectAtomsAndRewritesForLemmas(const IdToSatClause& lemmaClauses,
                                                std::set<Node>& atoms,
                                                NodePairSet& rewrites) {
  IdToSatClause::const_iterator it = lemmaClauses.begin();
  for (; it != lemmaClauses.end(); ++it) {
    const prop::SatClause* clause = it->second;

    // TODO: just calculate the map from ID to recipe once,
    // instead of redoing this over and over again
    std::vector<Expr> clause_expr;
    std::set<Node> clause_expr_nodes;
    for(unsigned i = 0; i < clause->size(); ++i) {
      prop::SatLiteral lit = (*clause)[i];
      Node node = getAtom(lit.getSatVariable());
      Expr atom = node.toExpr();
      if (atom.isConst()) {
        Assert(atom == utils::mkTrue());
        continue;
      }
      clause_expr_nodes.insert(lit.isNegated() ? node.notNode() : node);
    }

    LemmaProofRecipe recipe = getProofRecipe(clause_expr_nodes);

    for (unsigned i = 0; i < recipe.getNumSteps(); ++i) {
      const LemmaProofRecipe::ProofStep* proofStep = recipe.getStep(i);
      Node atom = proofStep->getLiteral();

      if (atom == Node()) {
        // The last proof step always has the empty node as its target...
        continue;
      }

      if (atom.getKind() == kind::NOT) {
        atom = atom[0];
      }

      atoms.insert(atom);
    }

    LemmaProofRecipe::RewriteIterator rewriteIt;
    for (rewriteIt = recipe.rewriteBegin(); rewriteIt != recipe.rewriteEnd(); ++rewriteIt) {
      rewrites.insert(NodePair(rewriteIt->first, rewriteIt->second));

      // The unrewritten terms also need to have literals, so insert them into atoms
      Node rewritten = rewriteIt->first;
      if (rewritten.getKind() == kind::NOT) {
        rewritten = rewritten[0];
      }
      atoms.insert(rewritten);
    }
  }
}

void CnfProof::collectAssertionsForClauses(const IdToSatClause& clauses,
                                           NodeSet& assertions) {
  IdToSatClause::const_iterator it = clauses.begin();
  for (; it != clauses.end(); ++it) {
    TNode used_assertion =  getAssertionForClause(it->first);
    assertions.insert(used_assertion);
    // it can be the case that a definition for a clause is an assertion
    // but it is not the assertion for the clause
    // e.g. the assertions [(and a b), a]
    TNode used_definition = getDefinitionForClause(it->first);
    if (isAssertion(used_definition)) {
      assertions.insert(used_definition);
    }
  }
}

// Detects whether a clause has x v ~x for some x
// If so, returns the positive occurence's idx first, then the negative's
Maybe<std::pair<size_t, size_t>> CnfProof::detectTrivialTautology(
    const prop::SatClause& clause)
{
  // a map from a SatVariable to its previous occurence's polarity and location
  std::map<prop::SatVariable, std::pair<bool, size_t>> varsToPolsAndIndices;
  for (size_t i = 0; i < clause.size(); ++i)
  {
    prop::SatLiteral lit = clause[i];
    prop::SatVariable var = lit.getSatVariable();
    bool polarity = !lit.isNegated();

    // Check if this var has already occured w/ opposite polarity
    auto iter = varsToPolsAndIndices.find(var);
    if (iter != varsToPolsAndIndices.end() && iter->second.first != polarity)
    {
      if (iter->second.first)
      {
        return Maybe<std::pair<size_t, size_t>>{
            std::make_pair(iter->second.second, i)};
      }
      else
      {
        return Maybe<std::pair<size_t, size_t>>{
            std::make_pair(i, iter->second.second)};
      }
    }
    varsToPolsAndIndices[var] = std::make_pair(polarity, i);
  }
  return Maybe<std::pair<size_t, size_t>>{};
}

void LFSCCnfProof::printAtomMapping(const std::set<Node>& atoms,
                                    std::ostream& os,
                                    std::ostream& paren) {
  std::set<Node>::const_iterator it = atoms.begin();
  std::set<Node>::const_iterator end = atoms.end();

  for (;it != end; ++it) {
    os << "(decl_atom ";
    Node atom = *it;
    prop::SatVariable var = getLiteral(atom).getSatVariable();
    //FIXME hideous
    LFSCTheoryProofEngine* pe = (LFSCTheoryProofEngine*)ProofManager::currentPM()->getTheoryProofEngine();
    pe->printLetTerm(atom.toExpr(), os);

    os << " (\\ " << ProofManager::getVarName(var, d_name);
    os << " (\\ " << ProofManager::getAtomName(var, d_name) << "\n";
    paren << ")))";
  }
}

void LFSCCnfProof::printAtomMapping(const std::set<Node>& atoms,
                                    std::ostream& os,
                                    std::ostream& paren,
                                    ProofLetMap &letMap) {
  std::set<Node>::const_iterator it = atoms.begin();
  std::set<Node>::const_iterator end = atoms.end();

  for (;it != end; ++it) {
    os << "(decl_atom ";
    Node atom = *it;
    prop::SatVariable var = getLiteral(atom).getSatVariable();
    //FIXME hideous
    LFSCTheoryProofEngine* pe = (LFSCTheoryProofEngine*)ProofManager::currentPM()->getTheoryProofEngine();
    if (pe->printsAsBool(atom.toExpr())) os << "(p_app ";
    pe->printBoundTerm(atom.toExpr(), os, letMap);
    if (pe->printsAsBool(atom.toExpr())) os << ")";

    os << " (\\ " << ProofManager::getVarName(var, d_name);
    os << " (\\ " << ProofManager::getAtomName(var, d_name) << "\n";
    paren << ")))";
  }
}

// maps each expr to the position it had in the clause and the polarity it had
Node LFSCCnfProof::clauseToNode(const prop::SatClause& clause,
                                std::map<Node, unsigned>& childIndex,
                                std::map<Node, bool>& childPol ) {
  std::vector< Node > children;
  for (unsigned i = 0; i < clause.size(); ++i) {
    prop::SatLiteral lit = clause[i];
    prop::SatVariable var = lit.getSatVariable();
    Node atom = getAtom(var);
    children.push_back( lit.isNegated() ? atom.negate() : atom );
    childIndex[atom] = i;
    childPol[atom] = !lit.isNegated();
  }
  return children.size()==1 ? children[0] :
         NodeManager::currentNM()->mkNode(kind::OR, children );
}

void LFSCCnfProof::printCnfProofForClause(ClauseId id,
                                          const prop::SatClause* clause,
                                          std::ostream& os,
                                          std::ostream& paren) {
  Debug("cnf-pf") << std::endl << std::endl << "LFSCCnfProof::printCnfProofForClause( " << id << " ) starting "
                  << std::endl;

  os << "(satlem _ _ ";
  std::ostringstream clause_paren;
  printClause(*clause, os, clause_paren);
  os << "(clausify_false ";

  // FIXMEEEEEEEEEEEE
  // os <<"trust)";
  // os << clause_paren.str()
  //    << " (\\ " << ProofManager::getInputClauseName(id, d_name) << "\n";
  // paren << "))";

  // return;

  Assert(clause->size() > 0);

  // If the clause contains x v ~x, it's easy!
  //
  // It's important to check for this case, because our other logic for
  // recording the location of variables in the clause assumes the clause is
  // not tautological
  Maybe<std::pair<size_t, size_t>> isTrivialTaut =
      detectTrivialTautology(*clause);
  if (isTrivialTaut.just())
  {
    size_t posIndexInClause = isTrivialTaut.value().first;
    size_t negIndexInClause = isTrivialTaut.value().second;
    Trace("cnf-pf") << "; Indices " << posIndexInClause << " (+) and "
                    << negIndexInClause << " (-) make this clause a tautology"
                    << std::endl;

    std::string proofOfPos =
        ProofManager::getLitName((*clause)[negIndexInClause], d_name);
    std::string proofOfNeg =
        ProofManager::getLitName((*clause)[posIndexInClause], d_name);
    os << "(contra _ " << proofOfPos << " " << proofOfNeg << ")";
  }
  else
  {
    Node base_assertion = getDefinitionForClause(id);

    // get the assertion for the clause id
    std::map<Node, unsigned> childIndex;
    std::map<Node, bool> childPol;
    Node assertion = clauseToNode(*clause, childIndex, childPol);
    // if there is no reason, construct assertion directly.   This can happen
    // for unit clauses.
    if (base_assertion.isNull())
    {
      base_assertion = assertion;
    }
    // os_base is proof of base_assertion
    std::stringstream os_base;

    // checks if tautological definitional clause or top-level clause
    // and prints the proof of the top-level formula
    bool is_input = printProofTopLevel(base_assertion, os_base);

    if (is_input)
    {
      Debug("cnf-pf") << std::endl
                      << "; base assertion is input. proof: " << os_base.str()
                      << std::endl;
    }

    // get base assertion with polarity
    bool base_pol = base_assertion.getKind() != kind::NOT;
    base_assertion = base_assertion.getKind() == kind::NOT ? base_assertion[0]
                                                           : base_assertion;

    std::map<Node, unsigned>::iterator itci = childIndex.find(base_assertion);
    bool is_in_clause = itci != childIndex.end();
    unsigned base_index = is_in_clause ? itci->second : 0;
    Trace("cnf-pf") << std::endl;
    Trace("cnf-pf") << "; input = " << is_input
                    << ", is_in_clause = " << is_in_clause << ", id = " << id
                    << ", assertion = " << assertion
                    << ", base assertion = " << base_assertion << std::endl;
    if (!is_input)
    {
      Assert(is_in_clause);
      prop::SatLiteral blit = (*clause)[base_index];
      os_base << ProofManager::getLitName(blit, d_name);
      base_pol = !childPol[base_assertion];  // WHY? if the case is =>
    }
    Trace("cnf-pf") << "; polarity of base assertion = " << base_pol
                    << std::endl;
    Trace("cnf-pf") << "; proof of base : " << os_base.str() << std::endl;

    bool success = false;
    if (is_input && is_in_clause && childPol[base_assertion] == base_pol)
    {
      // if both in input and in clause, the proof is trivial.  this is the case
      // for unit clauses.
      Trace("cnf-pf") << "; trivial" << std::endl;
      os << "(contra _ ";
      success = true;
      prop::SatLiteral lit = (*clause)[itci->second];
      if (base_pol)
      {
        os << os_base.str() << " " << ProofManager::getLitName(lit, d_name);
      }
      else
      {
        os << ProofManager::getLitName(lit, d_name) << " " << os_base.str();
      }
      os << ")";
    } else if ((base_assertion.getKind()==kind::AND && !base_pol) ||
           ((base_assertion.getKind()==kind::OR ||
             base_assertion.getKind()==kind::IMPLIES) && base_pol)) {
    Trace("cnf-pf") << "; and/or case 1" << std::endl;
    success = true;
    std::stringstream os_main;
    std::stringstream os_paren;
    //eliminate each one
    for (int j = base_assertion.getNumChildren()-2; j >= 0; j--) {
      Trace("cnf-pf-debug") << "; base_assertion[" << j << "] is: " << base_assertion[j]
                            << ", and its kind is: " << base_assertion[j].getKind() << std::endl ;

      Node child_base = base_assertion[j].getKind()==kind::NOT ?
                        base_assertion[j][0] : base_assertion[j];
      bool child_pol = base_assertion[j].getKind()!=kind::NOT;

      Trace("cnf-pf-debug") << "; child " << j << " "
                            << ", child base: " << child_base
                            << ", child pol: " << child_pol
                            << ", childPol[child_base] "
                            << childPol[child_base] << ", base pol: " << base_pol << std::endl;

      std::map< Node, unsigned >::iterator itcic = childIndex.find( child_base );

      if( itcic!=childIndex.end() ){
        //Assert( child_pol==childPol[child_base] );
        os_main << "(or_elim_1 _ _ ";
        prop::SatLiteral lit = (*clause)[itcic->second];
        // Should be if in the original formula it was negated
        // if( childPol[child_base] && base_pol ){

        // Adding the below to catch a specific case where the first child of an IMPLIES is negative,
        // in which case we need not_not introduction.
        if (base_assertion.getKind() == kind::IMPLIES && !child_pol && base_pol) {
          os_main << "(not_not_intro _ " << ProofManager::getLitName(lit, d_name) << ") ";
        } else if (childPol[child_base] && base_pol) {
          os_main << ProofManager::getLitName(lit, d_name) << " ";
        }else{
          os_main << "(not_not_intro _ " << ProofManager::getLitName(lit, d_name) << ") ";
        }
        if( base_assertion.getKind()==kind::AND ){
          os_main << "(not_and_elim _ _ ";
          os_paren << ")";
        }
        os_paren << ")";
      }else{
        success = false;
      }
    }

    if( success ){
      if( base_assertion.getKind()==kind::IMPLIES ){
        os_main << "(impl_elim _ _ ";
      }
      os_main << os_base.str();
      if( base_assertion.getKind()==kind::IMPLIES ){
        os_main << ")";
      }
      os_main << os_paren.str();
      int last_index = base_assertion.getNumChildren()-1;
      Node child_base = base_assertion[last_index].getKind()==kind::NOT ? base_assertion[last_index][0] : base_assertion[last_index];
      //bool child_pol = base_assertion[last_index].getKind()!=kind::NOT;
      std::map< Node, unsigned >::iterator itcic = childIndex.find( child_base );
      if( itcic!=childIndex.end() ){
        os << "(contra _ ";
        prop::SatLiteral lit = (*clause)[itcic->second];
        if( childPol[child_base] && base_pol){
          os << os_main.str() << " " << ProofManager::getLitName(lit, d_name);
        }else{
          os << ProofManager::getLitName(lit, d_name) << " " << os_main.str();
        }
        os << ")";
      }else{
        success = false;
      }
    }
  }else if ((base_assertion.getKind()==kind::AND && base_pol) ||
            ((base_assertion.getKind()==kind::OR ||
              base_assertion.getKind()==kind::IMPLIES) && !base_pol)) {

    std::stringstream os_main;

    Node iatom;
    if (is_in_clause) {
      Assert(assertion.getNumChildren() == 2);
      iatom = assertion[ base_index==0 ? 1 : 0];
    } else {
      Assert(assertion.getNumChildren() == 1);
      iatom = assertion[0];
    }

    Trace("cnf-pf") << "; and/or case 2, iatom = " << iatom << std::endl;
    Node e_base = iatom.getKind()==kind::NOT ? iatom[0] : iatom;
    bool e_pol = iatom.getKind()!=kind::NOT;
    std::map< Node, unsigned >::iterator itcic = childIndex.find( e_base );
    if( itcic!=childIndex.end() ){
      prop::SatLiteral lit = (*clause)[itcic->second];
      //eliminate until we find iatom
      for( unsigned j=0; j<base_assertion.getNumChildren(); j++ ){
        Node child_base = base_assertion[j].getKind()==kind::NOT ? base_assertion[j][0] : base_assertion[j];
        bool child_pol = base_assertion[j].getKind()!=kind::NOT;
        if( j==0 && base_assertion.getKind()==kind::IMPLIES ){
          child_pol = !child_pol;
        }
        if( e_base==child_base && (e_pol==child_pol)==(base_assertion.getKind()==kind::AND) ){
          success = true;
          bool elimNn =( ( base_assertion.getKind()==kind::OR || ( base_assertion.getKind()==kind::IMPLIES && j==1 ) ) && e_pol );
          if( elimNn ){
            os_main << "(not_not_elim _ ";
          }
          std::stringstream os_paren;
          if( j+1<base_assertion.getNumChildren() ){
            os_main << "(and_elim_1 _ _ ";
            if( base_assertion.getKind()==kind::OR || base_assertion.getKind()==kind::IMPLIES ){
              os_main << "(not_" << ( base_assertion.getKind()==kind::OR ? "or" : "impl" ) << "_elim _ _ ";
              os_paren << ")";
            }
            os_paren << ")";
          }
          for( unsigned k=0; k<j; k++ ){
            os_main << "(and_elim_2 _ _ ";
            if( base_assertion.getKind()==kind::OR || base_assertion.getKind()==kind::IMPLIES ){
              os_main << "(not_" << ( base_assertion.getKind()==kind::OR ? "or" : "impl" ) << "_elim _ _ ";
              os_paren << ")";
            }
            os_paren << ")";
          }
          os_main << os_base.str() << os_paren.str();
          if( elimNn ){
            os_main << ")";
          }
          break;
        }
      }
      if( success ){
        os << "(contra _ ";
        if( !e_pol ){
          os << ProofManager::getLitName(lit, d_name) << " " << os_main.str();
        }else{
          os << os_main.str() << " " << ProofManager::getLitName(lit, d_name);
        }
        os << ")";
      }
    }
  }else if( base_assertion.getKind()==kind::XOR || ( base_assertion.getKind()==kind::EQUAL && base_assertion[0].getType().isBoolean() ) ){
    //eliminate negation
    int num_nots_2 = 0;
    int num_nots_1 = 0;
    Kind k;
    if( !base_pol ){
      if( base_assertion.getKind()==kind::EQUAL ){
        num_nots_2 = 1;
      }
      k = kind::EQUAL;
    }else{
      k = base_assertion.getKind();
    }
    std::vector< unsigned > indices;
    std::vector< bool > pols;
    success = true;
    int elimNum = 0;
    for( unsigned i=0; i<2; i++ ){
      Node child_base = base_assertion[i].getKind()==kind::NOT ? base_assertion[i][0] : base_assertion[i];
      bool child_pol = base_assertion[i].getKind()!=kind::NOT;
      std::map< Node, unsigned >::iterator itcic = childIndex.find( child_base );
      if( itcic!=childIndex.end() ){
        indices.push_back( itcic->second );
        pols.push_back( childPol[child_base] );
        if( i==0 ){
          //figure out which way to elim
          elimNum = child_pol==childPol[child_base] ? 2 : 1;
          if( (elimNum==2)==(k==kind::EQUAL) ){
            num_nots_2++;
          }
          if( elimNum==1 ){
            num_nots_1++;
          }
        }
      }else{
        success = false;
        break;
      }
    }
    Trace("cnf-pf") << std::endl << "; num nots = " << num_nots_2 << std::endl;
    if( success ){
      os << "(contra _ ";
      std::stringstream os_base_n;
      if( num_nots_2==2 ){
        os_base_n << "(not_not_elim _ ";
      }
      os_base_n << "(or_elim_1 _ _ ";
      prop::SatLiteral lit1 = (*clause)[indices[0]];
      if( !pols[0] || num_nots_1==1 ){
        os_base_n << "(not_not_intro _ " << ProofManager::getLitName(lit1, d_name) << ") ";
      }else{
        Trace("cnf-pf-debug") << "CALLING getlitname" << std::endl;
        os_base_n << ProofManager::getLitName(lit1, d_name) << " ";
      }
      Assert(elimNum != 0);
      os_base_n << "(" << ( k==kind::EQUAL ? "iff" : "xor" ) << "_elim_" << elimNum << " _ _ ";
      if( !base_pol ){
        os_base_n << "(not_" << ( base_assertion.getKind()==kind::EQUAL ? "iff" : "xor" ) << "_elim _ _ " << os_base.str() << ")";
      }else{
        os_base_n << os_base.str();
      }
      os_base_n << "))";
      if( num_nots_2==2 ){
        os_base_n << ")";
        num_nots_2 = 0;
      }
      prop::SatLiteral lit2 = (*clause)[indices[1]];
      if( pols[1]==(num_nots_2==0) ){
        os << os_base_n.str() << " ";
        if( num_nots_2==1 ){
          os << "(not_not_intro _ " << ProofManager::getLitName(lit2, d_name) << ")";
        }else{
          os << ProofManager::getLitName(lit2, d_name);
        }
      }else{
        os << ProofManager::getLitName(lit2, d_name) << " " << os_base_n.str();
      }
      os << ")";
    }
  }else if( base_assertion.getKind()==kind::ITE ){
    std::map< unsigned, unsigned > appears;
    std::map< unsigned, Node > appears_expr;
    unsigned appears_count = 0;
    for( unsigned r=0; r<3; r++ ){
      Node child_base = base_assertion[r].getKind()==kind::NOT ? base_assertion[r][0] : base_assertion[r];
      std::map< Node, unsigned >::iterator itcic = childIndex.find( child_base );
      if( itcic!=childIndex.end() ){
        appears[r] = itcic->second;
        appears_expr[r] = child_base;
        appears_count++;
      }
    }
    if( appears_count==2 ){
      success = true;
      int elimNum = 1;
      unsigned index1 = 0;
      unsigned index2 = 1;
      if( appears.find( 0 )==appears.end() ){
        elimNum = 3;
        index1 = 1;
        index2 = 2;
      }else if( appears.find( 1 )==appears.end() ){
        elimNum = 2;
        index1 = 0;
        index2 = 2;
      }
      std::stringstream os_main;
      os_main << "(or_elim_1 _ _ ";
      prop::SatLiteral lit1 = (*clause)[appears[index1]];
      if( !childPol[appears_expr[index1]] || elimNum==1 || ( elimNum==3 && !base_pol ) ){
        os_main << "(not_not_intro _ " << ProofManager::getLitName(lit1, d_name) << ") ";
      }else{
        os_main << ProofManager::getLitName(lit1, d_name) << " ";
      }
      os_main << "(" << ( base_pol ? "" : "not_" ) << "ite_elim_" << elimNum << " _ _ _ ";
      os_main << os_base.str() << "))";
      os << "(contra _ ";
      prop::SatLiteral lit2 = (*clause)[appears[index2]];
      if( !childPol[appears_expr[index2]] || !base_pol ){
        os << ProofManager::getLitName(lit2, d_name) << " " << os_main.str();
      }else{
        os << os_main.str() << " " << ProofManager::getLitName(lit2, d_name);
      }
      os << ")";
    }
  }else if( base_assertion.isConst() ){
    bool pol = base_assertion==NodeManager::currentNM()->mkConst( true );
    if( pol!=base_pol ){
      success = true;
      if( pol ){
        os << "(contra _ truth " << os_base.str() << ")";
      }else{
        os << os_base.str();
      }
    }
  }

  if( !success ){
    Trace("cnf-pf") << std::endl;
    Trace("cnf-pf") << ";!!!!!!!!! CnfProof : Can't process " << assertion << ", base = " << base_assertion << ", id = " << id << std::endl;
    Trace("cnf-pf") << ";!!!!!!!!! Clause is : ";
    for (unsigned i = 0; i < clause->size(); ++i) {
      Trace("cnf-pf") << (*clause)[i] << " ";
    }
    Trace("cnf-pf") << std::endl;
    os << "trust-bad";
  }
  }

  os << ")" << clause_paren.str()
     << " (\\ " << ProofManager::getInputClauseName(id, d_name) << "\n";

  paren << "))";
}

void LFSCCnfProof::printClause(const prop::SatClause& clause,
                               std::ostream& os,
                               std::ostream& paren) {
  for (unsigned i = 0; i < clause.size(); ++i) {
    prop::SatLiteral lit = clause[i];
    prop::SatVariable var = lit.getSatVariable();
    if (lit.isNegated()) {
      os << "(ast _ _ _ " << ProofManager::getAtomName(var, d_name) <<" (\\ " << ProofManager::getLitName(lit, d_name) << " ";
      paren << "))";
    } else {
      os << "(asf _ _ _ " << ProofManager::getAtomName(var, d_name) <<" (\\ " << ProofManager::getLitName(lit, d_name) << " ";
      paren << "))";
    }
  }
}

// print a proof of the top-level formula e, based on the input assertions
bool LFSCCnfProof::printProofTopLevel(Node e, std::ostream& out) {
  if (!isAssertion(e)) {
    // check if deduced by CNF
    // dependence on top level fact i.e. a depends on (a and b)
    NodeToNode::const_iterator itd = d_cnfDeps.find(e);
    if (itd != d_cnfDeps.end()) {
      TNode parent = itd->second;
      //check if parent is an input assertion
      std::stringstream out_parent;
      if (printProofTopLevel(parent, out_parent)) {
        if(parent.getKind()==kind::AND ||
           (parent.getKind()==kind::NOT && (parent[0].getKind()==kind::IMPLIES ||
                                            parent[0].getKind()==kind::OR))) {
          Node parent_base = parent.getKind()==kind::NOT ? parent[0] : parent;
          Node e_base = e.getKind()==kind::NOT ? e[0] : e;
          bool e_pol = e.getKind()!=kind::NOT;
          for( unsigned i=0; i<parent_base.getNumChildren(); i++ ){
            Node child_base = parent_base[i].getKind()==kind::NOT ? parent_base[i][0] : parent_base[i];
            bool child_pol = parent_base[i].getKind()!=kind::NOT;
            if( parent_base.getKind()==kind::IMPLIES && i==0 ){
              child_pol = !child_pol;
            }
            if (e_base==child_base &&
                (e_pol==child_pol)==(parent_base.getKind()==kind::AND)) {
              bool elimNn = ((parent_base.getKind()==kind::OR ||
                              (parent_base.getKind()==kind::IMPLIES && i==1)) && e_pol);
              if (elimNn) {
                out << "(not_not_elim _ ";
              }
              std::stringstream out_paren;
              if (i+1 < parent_base.getNumChildren()) {
                out << "(and_elim_1 _ _ ";
                if( parent_base.getKind()==kind::OR ||
                    parent_base.getKind()==kind::IMPLIES  ){
                  out << "(not_" << ( parent_base.getKind()==kind::OR ? "or" : "impl" )
                      << "_elim _ _ ";
                  out_paren << ")";
                }
                out_paren << ")";
              }
              for( unsigned j=0; j<i; j++ ){
                out << "(and_elim_2 _ _ ";
                if( parent_base.getKind()==kind::OR || parent_base.getKind()==kind::IMPLIES ){
                  out << "(not_" << ( parent_base.getKind()==kind::OR ? "or" : "impl" ) << "_elim _ _ ";
                  out_paren << ")";
                }
                out_paren << ")";
              }
              out << out_parent.str();
              out << out_paren.str();
              if( elimNn ){
                out << ")";
              }
              return true;
            }
          }
        } else {
          Trace("cnf-pf-debug") << "; isInputAssertion : parent of " << e
                                << " is not correct type (" << parent << ")" << std::endl;
        }
      } else {
        Trace("cnf-pf-debug") << "; isInputAssertion : parent of " << e
                              << " is not input" << std::endl;
      }
    } else {
      Trace("cnf-pf-debug") << "; isInputAssertion : " << e
                            << " has no parent" << std::endl;
    }
    return false;
  } else {
    out << ProofManager::getPreprocessedAssertionName(e);
    return true;
  }
}

} /* CVC4 namespace */
