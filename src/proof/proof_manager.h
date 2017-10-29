/*********************                                                        */
/*! \file proof_manager.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Liana Hadarean, Guy Katz, Morgan Deters
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2017 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief A manager for Proofs
 **
 ** A manager for Proofs.
 **/

#include "cvc4_private.h"

#ifndef __CVC4__PROOF_MANAGER_H
#define __CVC4__PROOF_MANAGER_H

#include <iosfwd>
#include <memory>
#include <unordered_map>
#include <unordered_set>

#include "expr/node.h"
#include "context/cdhashset.h"
#include "context/cdhashmap.h"
#include "proof/clause_id.h"
#include "proof/proof.h"
#include "proof/proof_utils.h"
#include "proof/skolemization_manager.h"
#include "theory/logic_info.h"
#include "theory/substitutions.h"
#include "util/proof.h"


namespace CVC4 {

class SmtGlobals;

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

const ClauseId ClauseIdEmpty(-1);
const ClauseId ClauseIdUndef(-2);
const ClauseId ClauseIdError(-3);

template <class Solver> class TSatProof;
typedef TSatProof< CVC4::Minisat::Solver> CoreSatProof;

class CnfProof;
class RewriterProof;
class TheoryProofEngine;
class TheoryProof;
class UFProof;
class ArithProof;
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

typedef std::unordered_map<ClauseId, prop::SatClause*> IdToSatClause;
typedef context::CDHashSet<Expr, ExprHashFunction> CDExprSet;
typedef std::unordered_map<Node, std::vector<Node>, NodeHashFunction> NodeToNodes;
typedef context::CDHashMap<Node, std::vector<Node>, NodeHashFunction> CDNodeToNodes;
typedef std::unordered_set<ClauseId> IdHashSet;

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

class RewriteLogEntry {
public:
  RewriteLogEntry(unsigned ruleId, Node original, Node result)
    : d_ruleId(ruleId), d_original(original), d_result(result) {
  }

  unsigned getRuleId() const {
    return d_ruleId;
  }

  Node getOriginal() const {
    return d_original;
  }

  Node getResult() const {
    return d_result;
  }

private:
  unsigned d_ruleId;
  Node d_original;
  Node d_result;
};

class ProofManager {
  context::Context* d_context;

  CoreSatProof*  d_satProof;
  CnfProof*      d_cnfProof;
  TheoryProofEngine* d_theoryProof;

  // information that will need to be shared across proofs
  ExprSet    d_inputFormulas;
  std::map<Expr, std::string> d_inputFormulaToName;
  CDExprSet    d_inputCoreFormulas;
  CDExprSet    d_outputCoreFormulas;

  SkolemizationManager d_skolemizationManager;

  int d_nextId;

  std::unique_ptr<Proof> d_fullProof;
  ProofFormat d_format; // used for now only in debug builds

  CDNodeToNodes d_deps;

  std::set<Type> d_printedTypes;

  std::map<std::string, std::string> d_rewriteFilters;
  std::map<Node, std::string> d_assertionFilters;

  std::vector<RewriteLogEntry> d_rewriteLog;

protected:
  LogicInfo d_logic;

public:
  ProofManager(context::Context* context, ProofFormat format = LFSC);
  ~ProofManager();

  static ProofManager* currentPM();

  // initialization
  void         initSatProof(Minisat::Solver* solver);
  static void         initCnfProof(CVC4::prop::CnfStream* cnfStream,
                                   context::Context* ctx);
  static void         initTheoryProofEngine();

  // getting various proofs
  static const Proof& getProof(SmtEngine* smt);
  static CoreSatProof*  getSatProof();
  static CnfProof*      getCnfProof();
  static TheoryProofEngine* getTheoryProofEngine();
  static TheoryProof* getTheoryProof( theory::TheoryId id );
  static UFProof* getUfProof();
  static BitVectorProof* getBitVectorProof();
  static ArrayProof* getArrayProof();
  static ArithProof* getArithProof();

  static SkolemizationManager *getSkolemizationManager();

  // iterators over data shared by proofs
  typedef ExprSet::const_iterator assertions_iterator;

  // iterate over the assertions (these are arbitrary boolean formulas)
  assertions_iterator begin_assertions() const {
    return d_inputFormulas.begin();
  }
  assertions_iterator end_assertions() const { return d_inputFormulas.end(); }
  size_t num_assertions() const { return d_inputFormulas.size(); }
  bool have_input_assertion(const Expr& assertion) {
    return d_inputFormulas.find(assertion) != d_inputFormulas.end();
  }

  void ensureLiteral(Node node);

//---from Morgan---
  Node mkOp(TNode n);
  Node lookupOp(TNode n) const;
  bool hasOp(TNode n) const;

  std::map<Node, Node> d_ops;
  std::map<Node, Node> d_bops;
//---end from Morgan---


  // variable prefixes
  static std::string getInputClauseName(ClauseId id, const std::string& prefix = "");
  static std::string getLemmaClauseName(ClauseId id, const std::string& prefix = "");
  static std::string getLemmaName(ClauseId id, const std::string& prefix = "");
  static std::string getLearntClauseName(ClauseId id, const std::string& prefix = "");
  static std::string getPreprocessedAssertionName(Node node, const std::string& prefix = "");
  static std::string getAssertionName(Node node, const std::string& prefix = "");
  static std::string getInputFormulaName(const Expr& expr);

  static std::string getVarName(prop::SatVariable var, const std::string& prefix = "");
  static std::string getAtomName(prop::SatVariable var, const std::string& prefix = "");
  static std::string getAtomName(TNode atom, const std::string& prefix = "");
  static std::string getLitName(prop::SatLiteral lit, const std::string& prefix = "");
  static std::string getLitName(TNode lit, const std::string& prefix = "");
  static bool hasLitName(TNode lit);

  // for SMT variable names that have spaces and other things
  static std::string sanitize(TNode var);

  /** Add proof assertion - unlike addCoreAssertion this is post definition expansion **/
  void addAssertion(Expr formula);

  /** Public unsat core methods **/
  void addCoreAssertion(Expr formula);

  void addDependence(TNode n, TNode dep);
  void addUnsatCore(Expr formula);

  // trace dependences back to unsat core
  void traceDeps(TNode n, ExprSet* coreAssertions);
  void traceDeps(TNode n, CDExprSet* coreAssertions);
  void traceUnsatCore();

  typedef CDExprSet::const_iterator output_core_iterator;

  output_core_iterator begin_unsat_core() const { return d_outputCoreFormulas.begin(); }
  output_core_iterator end_unsat_core() const { return d_outputCoreFormulas.end(); }
  size_t size_unsat_core() const { return d_outputCoreFormulas.size(); }
  std::vector<Expr> extractUnsatCore();

  bool unsatCoreAvailable() const;
  void getLemmasInUnsatCore(theory::TheoryId theory, std::vector<Node> &lemmas);
  Node getWeakestImplicantInUnsatCore(Node lemma);

  int nextId() { return d_nextId++; }

  void setLogic(const LogicInfo& logic);
  const std::string getLogic() const { return d_logic.getLogicString(); }
  LogicInfo & getLogicInfo() { return d_logic; }

  void markPrinted(const Type& type);
  bool wasPrinted(const Type& type) const;

  void addRewriteFilter(const std::string &original, const std::string &substitute);
  void clearRewriteFilters();
  bool haveRewriteFilter(TNode lit);

  void addAssertionFilter(const Node& node, const std::string& rewritten);

  static void registerRewrite(unsigned ruleId, Node original, Node result);
  static void clearRewriteLog();

  std::vector<RewriteLogEntry> getRewriteLog();
  void dumpRewriteLog() const;

  void printGlobalLetMap(std::set<Node>& atoms,
                         ProofLetMap& letMap,
                         std::ostream& out,
                         std::ostringstream& paren);

private:
  void constructSatProof();
  std::set<Node> satClauseToNodeSet(prop::SatClause* clause);
};/* class ProofManager */

class LFSCProof : public Proof
{
 public:
  LFSCProof(SmtEngine* smtEngine,
            LFSCCoreSatProof* sat,
            LFSCCnfProof* cnf,
            LFSCTheoryProofEngine* theory);
  ~LFSCProof() override {}
  void toStream(std::ostream& out) const override;
  void toStream(std::ostream& out, const ProofLetMap& map) const override;

 private:
  // FIXME: hack until we get preprocessing
  void printPreprocessedAssertions(const NodeSet& assertions,
                                   std::ostream& os,
                                   std::ostream& paren,
                                   ProofLetMap& globalLetMap) const;

  void checkUnrewrittenAssertion(const NodeSet& assertions) const;

  LFSCCoreSatProof* d_satProof;
  LFSCCnfProof* d_cnfProof;
  LFSCTheoryProofEngine* d_theoryProof;
  SmtEngine* d_smtEngine;
}; /* class LFSCProof */

std::ostream& operator<<(std::ostream& out, CVC4::ProofRule k);
}/* CVC4 namespace */



#endif /* __CVC4__PROOF_MANAGER_H */
