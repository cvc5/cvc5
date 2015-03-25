/*********************                                                        */
/*! \file proof_manager.h
 ** \verbatim
 ** Original author: Liana Hadarean
 ** Major contributors: Morgan Deters
 ** Minor contributors (to current version): none
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

#include <iostream>
#include <map>
#include "proof/proof.h"
#include "util/proof.h"
#include "expr/node.h"
#include "theory/logic_info.h"
#include "theory/substitutions.h"

// forward declarations
namespace Minisat {
  class Solver;
}/* Minisat namespace */

namespace BVMinisat {
  class Solver;
}/* BVMinisat namespace */


namespace CVC4 {

namespace prop {
  class CnfStream;
}/* CVC4::prop namespace */

class SmtEngine;

typedef int ClauseId;

class Proof;
template <class Solver> class TSatProof; 
typedef TSatProof< ::Minisat::Solver> CoreSatProof;
//typedef TSatProof< ::BVMinisat::Solver> BVSatProof;
class CnfProof;
class RewriterProof;
class TheoryProofEngine;
class UFProof;
class ArrayProof;
class BitVectorProof;

template <class Solver> class LFSCSatProof; 
typedef LFSCSatProof< ::Minisat::Solver> LFSCCoreSatProof;
//typedef LFSCSatProof< ::BVMinisat::Solver> LFSCBVSatProof;
class LFSCCnfProof;
class LFSCTheoryProofEngine;
class LFSCUFProof;
class LFSCBitVectorProof;
class LFSCRewriterProof;

template <class Solver> class ProofProxy;
typedef ProofProxy< ::Minisat::Solver> CoreProofProxy;
typedef ProofProxy< ::BVMinisat::Solver> BVProofProxy; 

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

typedef __gnu_cxx::hash_map < ClauseId, const prop::SatClause* > IdToClause;
typedef std::map < ClauseId, const prop::SatClause* > OrderedIdToClause;
typedef __gnu_cxx::hash_set<prop::SatVariable > VarSet;

typedef __gnu_cxx::hash_set<Expr, ExprHashFunction > ExprSet;
typedef __gnu_cxx::hash_set<prop::SatVariable> SatVarSet;
typedef __gnu_cxx::hash_map < ClauseId, const prop::SatClause* > IdToClause;

typedef int ClauseId;

enum ClauseKind {
  INPUT,
  THEORY_LEMMA,
  LEARNT
};/* enum ClauseKind */

enum ProofRule {
  RULE_GIVEN,       /* input assertion */
  RULE_DERIVED,     /* a "macro" rule */
  RULE_RECONSTRUCT, /* prove equivalence using another method */
  RULE_TRUST,       /* trust without evidence (escape hatch until proofs are fully supported) */
  RULE_INVALID,     /* assert-fail if this is ever needed in proof; use e.g. for split lemmas */
  RULE_CONFLICT,    /* re-construct as a conflict */

  RULE_ARRAYS_EXT,  /* arrays, extensional */
  RULE_ARRAYS_ROW,  /* arrays, read-over-write */
};/* enum ProofRules */

class ProofManager {
  CoreSatProof*  d_satProof;
  CnfProof*      d_cnfProof;
  RewriterProof* d_rewriterProof;
  TheoryProofEngine* d_theoryProof;

  // information that will need to be shared across proofs
  IdToClause d_inputClauses;
  OrderedIdToClause d_theoryLemmas;
  IdToClause d_theoryPropagations;
  ExprSet    d_inputFormulas;
  ExprSet    d_inputCoreFormulas;
  ExprSet    d_outputCoreFormulas;
  //VarSet     d_propVars;

  int d_nextId;

  Proof* d_fullProof;
  ProofFormat d_format; // used for now only in debug builds

  __gnu_cxx::hash_map< Node, std::vector<Node>, NodeHashFunction > d_deps;

  // trace dependences back to unsat core
  void traceDeps(TNode n);

protected:
  LogicInfo d_logic;

public:
  ProofManager(ProofFormat format = LFSC);
  ~ProofManager();

  static ProofManager* currentPM();

  // initialization
  static void         initSatProof(Minisat::Solver* solver);
  static void         initCnfProof(CVC4::prop::CnfStream* cnfStream);
  static void         initTheoryProofEngine();
  static void         initRewriterProof();
  // getting various proofs
  static Proof*         getProof(SmtEngine* smt);
  static CoreSatProof*  getSatProof();
  static CnfProof*      getCnfProof();
  static TheoryProofEngine* getTheoryProofEngine();
  static RewriterProof* getRewriterProof();
  static UFProof* getUfProof();
  static BitVectorProof* getBitVectorProof();
  static ArrayProof* getArrayProof();
  
  // iterators over data shared by proofs
  typedef IdToClause::const_iterator clause_iterator;
  typedef OrderedIdToClause::const_iterator ordered_clause_iterator;
  typedef ExprSet::const_iterator assertions_iterator;
  typedef VarSet::const_iterator var_iterator;

  clause_iterator begin_input_clauses() const { return d_inputClauses.begin(); }
  clause_iterator end_input_clauses() const { return d_inputClauses.end(); }
  size_t num_input_clauses() const { return d_inputClauses.size(); }

  ordered_clause_iterator begin_lemmas() const { return d_theoryLemmas.begin(); }
  ordered_clause_iterator end_lemmas() const { return d_theoryLemmas.end(); }
  size_t num_lemmas() const { return d_theoryLemmas.size(); }

  // iterate over the assertions (these are arbitrary boolean formulas)
  assertions_iterator begin_assertions() const { return d_inputFormulas.begin(); }
  assertions_iterator end_assertions() const { return d_inputFormulas.end(); }
  size_t num_assertions() const { return d_inputFormulas.size(); }

  
  void addAssertion(Expr formula, bool inUnsatCore);
  void addTheoryLemma(ClauseId id, const prop::SatClause* clause);
  void addClause(ClauseId id, const prop::SatClause* clause, ClauseKind kind);
  // note that n depends on dep (for cores)
  void addDependence(TNode n, TNode dep);
  
  // variable prefixes
  static std::string getInputClauseName(ClauseId id, const std::string& prefix = "");
  static std::string getLemmaClauseName(ClauseId id, const std::string& prefix = "");
  static std::string getLemmaName(ClauseId id, const std::string& prefix = "");
  static std::string getLearntClauseName(ClauseId id, const std::string& prefix = "");

  static std::string getVarName(prop::SatVariable var, const std::string& prefix = "");
  static std::string getAtomName(prop::SatVariable var, const std::string& prefix = "");
  static std::string getAtomName(TNode atom, const std::string& prefix = "");
  static std::string getLitName(prop::SatLiteral lit, const std::string& prefix = "");
  static std::string getLitName(TNode lit, const std::string& prefix = "");
  
  void printProof(std::ostream& os, TNode n);

  assertions_iterator begin_unsat_core() const { return d_outputCoreFormulas.begin(); }
  assertions_iterator end_unsat_core() const { return d_outputCoreFormulas.end(); }
  size_t size_unsat_core() const { return d_outputCoreFormulas.size(); }

  int nextId() { return d_nextId++; }

  void setLogic(const LogicInfo& logic);
  const std::string getLogic() const { return d_logic.getLogicString(); }

};/* class ProofManager */

class LFSCProof : public Proof {
  LFSCCnfProof* d_cnfProof;
  LFSCCoreSatProof* d_satProof;
  LFSCRewriterProof* d_rewriterProof;
  LFSCTheoryProofEngine* d_theoryProof;
  SmtEngine* d_smtEngine;
public:
  LFSCProof(SmtEngine* smtEngine,
            LFSCCoreSatProof* sat,
            LFSCCnfProof* cnf,
            LFSCRewriterProof* rwr,
            LFSCTheoryProofEngine* theory);
  virtual void toStream(std::ostream& out);
  virtual ~LFSCProof() {}
};/* class LFSCProof */

}/* CVC4 namespace */

#endif /* __CVC4__PROOF_MANAGER_H */
