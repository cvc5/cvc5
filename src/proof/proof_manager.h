/*********************                                                        */
/*! \file proof_manager.h
 ** \verbatim
 ** Original author: Liana Hadarean
 ** Major contributors: Morgan Deters
 ** Minor contributors (to current version): Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2014  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief A manager for Proofs
 **
 ** A manager for Proofs.
 **/

#include "cvc4_private.h"

#ifndef __CVC4__PROOF_MANAGER_H
#define __CVC4__PROOF_MANAGER_H

#include <iosfwd>
#include <map>

#include "expr/node.h"
#include "proof/proof.h"
#include "theory/logic_info.h"
#include "theory/substitutions.h"
#include "util/proof.h"


namespace CVC4 {

// forward declarations
namespace Minisat {
  class Solver;
}/* Minisat namespace */

namespace BVMinisat {
  class Solver;
}/* BVMinisat namespace */

namespace prop {
  class CnfStream;
}/* CVC4::prop namespace */

class SmtEngine;

typedef unsigned ClauseId;
const ClauseId ClauseIdEmpty(-1);
const ClauseId ClauseIdUndef(-2);  
const ClauseId ClauseIdError(-3);

class Proof;
template <class Solver> class TSatProof; 
typedef TSatProof< CVC4::Minisat::Solver> CoreSatProof;

class CnfProof;
class RewriterProof;
class TheoryProofEngine;
class TheoryProof;
class UFProof;
class ArrayProof;
class BitVectorProof;

template <class Solver> class LFSCSatProof; 
typedef LFSCSatProof< CVC4::Minisat::Solver> LFSCCoreSatProof;

class LFSCCnfProof;
class LFSCTheoryProofEngine;
class LFSCUFProof;
class LFSCBitVectorProof;
class LFSCRewriterProof;

template <class Solver> class ProofProxy;
typedef ProofProxy< CVC4::Minisat::Solver> CoreProofProxy;
typedef ProofProxy< CVC4::BVMinisat::Solver> BVProofProxy; 

namespace prop {
  typedef uint64_t SatVariable;
  class SatLiteral;
  typedef std::vector<SatLiteral> SatClause;
}/* CVC4::prop namespace */

// different proof modes
enum ProofFormat {
  LFSC,
  NATIVE
};/* enum ProofFormat */

std::string append(const std::string& str, uint64_t num);

typedef std::map < ClauseId, const prop::SatClause* > OrderedIdToClause;
typedef __gnu_cxx::hash_map < ClauseId, prop::SatClause* > IdToSatClause;
typedef __gnu_cxx::hash_set<Expr, ExprHashFunction > ExprSet;
typedef __gnu_cxx::hash_set<Node, NodeHashFunction > NodeSet;
typedef __gnu_cxx::hash_map<Node, std::vector<Node>, NodeHashFunction > NodeToNodes;
typedef std::hash_set<ClauseId> IdHashSet;

typedef unsigned ClauseId;

enum ProofRule {
  RULE_GIVEN,       /* input assertion */
  RULE_DERIVED,     /* a "macro" rule */
  RULE_RECONSTRUCT, /* prove equivalence using another method */
  RULE_TRUST,       /* trust without evidence (escape hatch until proofs are fully supported) */
  RULE_INVALID,     /* assert-fail if this is ever needed in proof; use e.g. for split lemmas */
  RULE_CONFLICT,    /* re-construct as a conflict */
  RULE_TSEITIN,     /* Tseitin CNF transformation */
  RULE_SPLIT,       /* A splitting lemma of the form a v ~ a*/
  
  RULE_ARRAYS_EXT,  /* arrays, extensional */
  RULE_ARRAYS_ROW,  /* arrays, read-over-write */
};/* enum ProofRules */

class ProofManager {
  CoreSatProof*  d_satProof;
  CnfProof*      d_cnfProof;
  //  RewriterProof* d_rewriterProof;
  TheoryProofEngine* d_theoryProof;

  // information that will need to be shared across proofs
  IdToSatClause d_inputClauses;
  //  OrderedIdToSatClause d_theoryLemmas;
  //  IdToSatClause d_theoryPropagations;
  ExprSet    d_inputFormulas;
  ExprSet    d_inputCoreFormulas;
  ExprSet    d_outputCoreFormulas;
  //VarSet     d_propVars;

  int d_nextId;

  Proof* d_fullProof;
  ProofFormat d_format; // used for now only in debug builds

  NodeToNodes d_deps;
  // trace dependences back to unsat core
  void traceDeps(TNode n);

  // Node d_registering_assertion;
  // ProofRule d_registering_rule;
  // std::map< ClauseId, Expr > d_clause_id_to_assertion; // clause to top-level assertion 
  // std::map< ClauseId, ProofRule > d_clause_id_to_rule;
  // std::map< Expr, Expr > d_cnf_dep; // dependence of cnf top-level things
  //LFSC number for assertions
  // unsigned d_assertion_counter;
  // std::map< Expr, unsigned > d_assertion_to_id; // unsat core deps and preprocessed things
protected:
  LogicInfo d_logic;

public:
  ProofManager(ProofFormat format = LFSC);
  ~ProofManager();

  static ProofManager* currentPM();

  // initialization
  static void         initSatProof(Minisat::Solver* solver);
  static void         initCnfProof(CVC4::prop::CnfStream* cnfStream,
                                   context::Context* ctx);
  static void         initTheoryProofEngine();

  // getting various proofs
  static Proof*         getProof(SmtEngine* smt);
  static CoreSatProof*  getSatProof();
  static CnfProof*      getCnfProof();
  static TheoryProofEngine* getTheoryProofEngine();
  static RewriterProof* getRewriterProof();
  static TheoryProof* getTheoryProof( theory::TheoryId id );
  static UFProof* getUfProof();
  static BitVectorProof* getBitVectorProof();
  static ArrayProof* getArrayProof();
  
  // iterators over data shared by proofs
  typedef IdToSatClause::const_iterator clause_iterator;
  typedef OrderedIdToClause::const_iterator ordered_clause_iterator;
  typedef ExprSet::const_iterator assertions_iterator;


  // NodeToNodes::const_iterator begin_deps() const { return d_deps.begin(); }
  // NodeToNodes::const_iterator end_deps() const { return d_deps.end(); }

  // clause_iterator begin_input_clauses() const { return d_inputClauses.begin(); }
  // clause_iterator end_input_clauses() const { return d_inputClauses.end(); }
  // size_t num_input_clauses() const { return d_inputClauses.size(); }

  // iterate over theory lemmas (these are SAT clauses)
  // ordered_clause_iterator begin_lemmas() const { return d_theoryLemmas.begin(); }
  // ordered_clause_iterator end_lemmas() const { return d_theoryLemmas.end(); }
  // size_t num_lemmas() const { return d_theoryLemmas.size(); }

  // iterate over the assertions (these are arbitrary boolean formulas)
  assertions_iterator begin_assertions() const { return d_inputFormulas.begin(); }
  assertions_iterator end_assertions() const { return d_inputFormulas.end(); }
  size_t num_assertions() const { return d_inputFormulas.size(); }
  
//---from Morgan---
  Node mkOp(TNode n);
  Node lookupOp(TNode n) const;
  bool hasOp(TNode n) const;
  
  std::map<Node, Node> d_ops;
  std::map<Node, Node> d_bops;
//---end from Morgan---
  
  // void addTheoryLemma(ClauseId id, const prop::SatClause* clause, ClauseKind kind);
  //void addClause(ClauseId id, const prop::SatClause* clause, ClauseKind kind);
  
  // variable prefixes
  static std::string getInputClauseName(ClauseId id, const std::string& prefix = "");
  static std::string getLemmaClauseName(ClauseId id, const std::string& prefix = "");
  static std::string getLemmaName(ClauseId id, const std::string& prefix = "");
  static std::string getLearntClauseName(ClauseId id, const std::string& prefix = "");
  static std::string getPreprocessedAssertionName(Node node, const std::string& prefix = "");
  static std::string getAssertionName(Node node, const std::string& prefix = "");
  
  static std::string getVarName(prop::SatVariable var, const std::string& prefix = "");
  static std::string getAtomName(prop::SatVariable var, const std::string& prefix = "");
  static std::string getAtomName(TNode atom, const std::string& prefix = "");
  static std::string getLitName(prop::SatLiteral lit, const std::string& prefix = "");
  static std::string getLitName(TNode lit, const std::string& prefix = "");

  // for SMT variable names that have spaces and other things
  static std::string sanitize(TNode var);
  
  //  void printProof(std::ostream& os, TNode n);

  /** Add proof assertion - unlinke addCoreAssertion this is post definition expansion **/
  void addAssertion(Expr formula);
  
  /** Public unsat core methods **/
  void addCoreAssertion(Expr formula);
  
  void addDependence(TNode n, TNode dep);
  void addUnsatCore(Expr formula);

  void traceUnsatCore();
  assertions_iterator begin_unsat_core() const { return d_outputCoreFormulas.begin(); }
  assertions_iterator end_unsat_core() const { return d_outputCoreFormulas.end(); }
  size_t size_unsat_core() const { return d_outputCoreFormulas.size(); }

  int nextId() { return d_nextId++; }

  void setLogic(const LogicInfo& logic);
  const std::string getLogic() const { return d_logic.getLogicString(); }
  LogicInfo & getLogicInfo() { return d_logic; }

  // void setCnfDep(Expr child, Expr parent );
  // Expr getFormulaForClauseId(ClauseId id );
  // ProofRule getProofRuleForClauseId( ClauseId id );
  // unsigned getAssertionCounter() { return d_assertion_counter; }
  // void setAssertion( Expr e );
  // bool isInputAssertion( Expr e, std::ostream& out );

public:  // AJR : FIXME this is hacky
  //currently, to map between ClauseId and Expr, requires:
  // (1) CnfStream::assertClause(...) to call setRegisteringFormula,
  // (2) SatProof::registerClause(...)/registerUnitClause(...) to call setRegisteredClauseId.
  //this is under the assumption that the first call at (2) is invoked for the clause corresponding to the Expr at (1).
  // void setRegisteringFormula( Node n, ProofRule proof_id );
  // void setRegisteredClauseId( ClauseId id );
};/* class ProofManager */

class LFSCProof : public Proof {
  LFSCCoreSatProof* d_satProof;
  LFSCCnfProof* d_cnfProof;
  //  LFSCRewriterProof* d_rewriterProof;
  LFSCTheoryProofEngine* d_theoryProof;
  SmtEngine* d_smtEngine;
  // FIXME: hack until we get preprocessing
  void printPreprocessedAssertions(const NodeSet& assertions,
                                   std::ostream& os,
                                   std::ostream& paren);
public:
  LFSCProof(SmtEngine* smtEngine,
            LFSCCoreSatProof* sat,
            LFSCCnfProof* cnf,
            //      LFSCRewriterProof* rwr,
            LFSCTheoryProofEngine* theory);
  virtual void toStream(std::ostream& out);
  virtual ~LFSCProof() {}
};/* class LFSCProof */

inline std::ostream& operator<<(std::ostream& out, CVC4::ProofRule k) {
  switch(k) {
  case RULE_GIVEN:
    out << "RULE_GIVEN"; 
    break;
  case RULE_DERIVED:
    out << "RULE_DERIVED"; 
    break;
  case RULE_RECONSTRUCT:
    out << "RULE_RECONSTRUCT"; 
    break;
  case RULE_TRUST:
    out << "RULE_TRUST"; 
    break;
  case RULE_INVALID:
    out << "RULE_INVALID"; 
    break;
  case RULE_CONFLICT:
    out << "RULE_CONFLICT"; 
    break;
  case RULE_TSEITIN:
    out << "RULE_TSEITIN"; 
    break;
  case RULE_SPLIT:
    out << "RULE_SPLIT"; 
    break;
  case RULE_ARRAYS_EXT:
    out << "RULE_ARRAYS"; 
    break;
  case RULE_ARRAYS_ROW:
    out << "RULE_ARRAYS"; 
    break;
  default:
    out << "ProofRule Unknown! [" << unsigned(k) << "]";
  }

  return out;
}

}/* CVC4 namespace */



#endif /* __CVC4__PROOF_MANAGER_H */
