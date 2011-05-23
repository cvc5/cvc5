/*********************                                                        */
/*! \file smt_engine.cpp
 ** \verbatim
 ** Original author: mdeters
 ** Major contributors: dejan
 ** Minor contributors (to current version): cconway
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010, 2011  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief The main entry point into the CVC4 library's SMT interface
 **
 ** The main entry point into the CVC4 library's SMT interface.
 **/

#include <vector>
#include <string>
#include <utility>
#include <sstream>
#include <ext/hash_map>

#include "context/cdlist.h"
#include "context/cdset.h"
#include "context/context.h"
#include "expr/command.h"
#include "expr/expr.h"
#include "expr/node_builder.h"
#include "prop/prop_engine.h"
#include "smt/bad_option_exception.h"
#include "smt/modal_exception.h"
#include "smt/no_such_function_exception.h"
#include "smt/smt_engine.h"
#include "theory/theory_engine.h"
#include "util/boolean_simplification.h"
#include "util/configuration.h"
#include "util/exception.h"
#include "util/options.h"
#include "util/output.h"
#include "util/hash.h"
#include "theory/substitutions.h"
#include "theory/builtin/theory_builtin.h"
#include "theory/booleans/theory_bool.h"
#include "theory/uf/theory_uf.h"
#include "theory/uf/morgan/theory_uf_morgan.h"
#include "theory/uf/tim/theory_uf_tim.h"
#include "theory/arith/theory_arith.h"
#include "theory/arrays/theory_arrays.h"
#include "theory/bv/theory_bv.h"
#include "theory/datatypes/theory_datatypes.h"

using namespace std;
using namespace CVC4;
using namespace CVC4::smt;
using namespace CVC4::prop;
using namespace CVC4::context;

namespace CVC4 {

namespace smt {

/**
 * Representation of a defined function.  We keep these around in
 * SmtEngine to permit expanding definitions late (and lazily), to
 * support getValue() over defined functions, to support user output
 * in terms of defined functions, etc.
 */
class DefinedFunction {
  Node d_func;
  std::vector<Node> d_formals;
  Node d_formula;
public:
  DefinedFunction() {}
  DefinedFunction(Node func, vector<Node> formals, Node formula) :
    d_func(func),
    d_formals(formals),
    d_formula(formula) {
  }
  Node getFunction() const { return d_func; }
  vector<Node> getFormals() const { return d_formals; }
  Node getFormula() const { return d_formula; }
};/* class DefinedFunction */

/**
 * This is an inelegant solution, but for the present, it will work.
 * The point of this is to separate the public and private portions of
 * the SmtEngine class, so that smt_engine.h doesn't
 * #include "expr/node.h", which is a private CVC4 header (and can lead
 * to linking errors due to the improper inlining of non-visible symbols
 * into user code!).
 *
 * The "real" solution (that which is usually implemented) is to move
 * ALL the implementation to SmtEnginePrivate and maintain a
 * heap-allocated instance of it in SmtEngine.  SmtEngine (the public
 * one) becomes an "interface shell" which simply acts as a forwarder
 * of method calls.
 */
class SmtEnginePrivate {
  SmtEngine& d_smt;

  vector<Node> d_assertionsToSimplify;
  vector<Node> d_assertionsToPushToSat;

  theory::Substitutions d_topLevelSubstitutions;

  /**
   * Adjust the currently "withheld" assertions for the current
   * Options scope's SimplificationMode if purge is false, or push
   * them all out to the prop layer if purge is true.
   */
  void adjustAssertions(bool purge = false);

public:

  SmtEnginePrivate(SmtEngine& smt) : d_smt(smt) { }

  /**
   * Push withheld assertions out to the propositional layer, if any.
   */
  void pushAssertions() {
    Trace("smt") << "SMT pushing all withheld assertions" << endl;

    adjustAssertions(true);
    Assert(d_assertionsToSimplify.empty());
    Assert(d_assertionsToPushToSat.empty());

    Trace("smt") << "SMT done pushing all withheld assertions" << endl;
  }

  /**
   * Perform non-clausal simplification of a Node.  This involves
   * Theory implementations, but does NOT involve the SAT solver in
   * any way.
   */
  Node simplify(TNode n, bool noPersist = false)
    throw(NoSuchFunctionException, AssertionException);

  /**
   * Perform preprocessing of a Node.  This involves ITE removal and
   * Theory-specific rewriting, but NO action by the SAT solver.
   */
  Node preprocess(TNode n)
    throw(AssertionException);

  /**
   * Adds a formula to the current context.  Action here depends on
   * the SimplificationMode (in the current Options scope); the
   * formula might be pushed out to the propositional layer
   * immediately, or it might be simplified and kept, or it might not
   * even be simplified.
   */
  void addFormula(TNode n)
    throw(NoSuchFunctionException, AssertionException);

  /**
   * Expand definitions in n.
   */
  Node expandDefinitions(TNode n, hash_map<TNode, Node, TNodeHashFunction>& cache)
    throw(NoSuchFunctionException, AssertionException);
};/* class SmtEnginePrivate */

}/* namespace CVC4::smt */

using namespace CVC4::smt;

SmtEngine::SmtEngine(ExprManager* em) throw(AssertionException) :
  d_context(em->getContext()),
  d_userContext(new Context()),
  d_exprManager(em),
  d_nodeManager(d_exprManager->getNodeManager()),
  d_private(new smt::SmtEnginePrivate(*this)),
  d_definitionExpansionTime("smt::SmtEngine::definitionExpansionTime"),
  d_nonclausalSimplificationTime("smt::SmtEngine::nonclausalSimplificationTime"),
  d_staticLearningTime("smt::SmtEngine::staticLearningTime") {

  NodeManagerScope nms(d_nodeManager);

  StatisticsRegistry::registerStat(&d_definitionExpansionTime);
  StatisticsRegistry::registerStat(&d_nonclausalSimplificationTime);
  StatisticsRegistry::registerStat(&d_staticLearningTime);

  // We have mutual dependancy here, so we add the prop engine to the theory
  // engine later (it is non-essential there)
  d_theoryEngine = new TheoryEngine(d_context);

  // Add the theories
  d_theoryEngine->addTheory<theory::builtin::TheoryBuiltin>();
  d_theoryEngine->addTheory<theory::booleans::TheoryBool>();
  d_theoryEngine->addTheory<theory::arith::TheoryArith>();
  d_theoryEngine->addTheory<theory::arrays::TheoryArrays>();
  d_theoryEngine->addTheory<theory::bv::TheoryBV>();
  d_theoryEngine->addTheory<theory::datatypes::TheoryDatatypes>();
  switch(Options::current()->uf_implementation) {
  case Options::TIM:
    d_theoryEngine->addTheory<theory::uf::tim::TheoryUFTim>();
    break;
  case Options::MORGAN:
    d_theoryEngine->addTheory<theory::uf::morgan::TheoryUFMorgan>();
    break;
  default:
    Unhandled(Options::current()->uf_implementation);
  }

  d_propEngine = new PropEngine(d_theoryEngine, d_context);
  d_theoryEngine->setPropEngine(d_propEngine);

  d_definedFunctions = new(true) DefinedFunctionMap(d_userContext);

  d_assertionList = NULL;
  if(Options::current()->interactive) {
    d_assertionList = new(true) AssertionList(d_userContext);
  }

  d_assignments = NULL;
  d_haveAdditions = false;
  d_queryMade = false;
}

void SmtEngine::shutdown() {
  d_propEngine->shutdown();
  d_theoryEngine->shutdown();
}

SmtEngine::~SmtEngine() {
  NodeManagerScope nms(d_nodeManager);

  shutdown();

  if(d_assignments != NULL) {
    d_assignments->deleteSelf();
  }

  if(d_assertionList != NULL) {
    d_assertionList->deleteSelf();
  }

  d_definedFunctions->deleteSelf();

  StatisticsRegistry::unregisterStat(&d_definitionExpansionTime);
  StatisticsRegistry::unregisterStat(&d_nonclausalSimplificationTime);
  StatisticsRegistry::unregisterStat(&d_staticLearningTime);

  delete d_userContext;

  delete d_theoryEngine;
  delete d_propEngine;
}

void SmtEngine::setLogic(const std::string& s) throw(ModalException) {
  if(d_logic != "") {
    throw ModalException("logic already set");
  }
  d_logic = s;
  d_theoryEngine->d_logic = s;
}

void SmtEngine::setInfo(const std::string& key, const SExpr& value)
  throw(BadOptionException, ModalException) {
  Trace("smt") << "SMT setInfo(" << key << ", " << value << ")" << endl;
  if(key == ":name" ||
     key == ":source" ||
     key == ":category" ||
     key == ":difficulty" ||
     key == ":smt-lib-version" ||
     key == ":notes") {
    // ignore these
    return;
  } else if(key == ":status") {
    string s;
    if(value.isAtom()) {
      s = value.getValue();
    }
    if(s != "sat" && s != "unsat" && s != "unknown") {
      throw BadOptionException("argument to (set-info :status ..) must be "
                               "`sat' or `unsat' or `unknown'");
    }
    d_status = Result(s);
    return;
  }
  throw BadOptionException();
}

SExpr SmtEngine::getInfo(const std::string& key) const
  throw(BadOptionException) {
  Trace("smt") << "SMT getInfo(" << key << ")" << endl;
  if(key == ":all-statistics") {
    vector<SExpr> stats;
    for(StatisticsRegistry::const_iterator i = StatisticsRegistry::begin();
        i != StatisticsRegistry::end();
        ++i) {
      vector<SExpr> v;
      v.push_back((*i)->getName());
      v.push_back((*i)->getValue());
      stats.push_back(v);
    }
    return stats;
  } else if(key == ":error-behavior") {
    return SExpr("immediate-exit");
  } else if(key == ":name") {
    return Configuration::getName();
  } else if(key == ":version") {
    return Configuration::getVersionString();
  } else if(key == ":authors") {
    return Configuration::about();
  } else if(key == ":status") {
    return d_status.asSatisfiabilityResult().toString();
  } else if(key == ":reason-unknown") {
    if(d_status.isUnknown()) {
      stringstream ss;
      ss << d_status.whyUnknown();
      return ss.str();
    } else {
      throw ModalException("Can't get-info :reason-unknown when the "
                           "last result wasn't unknown!");
    }
  } else {
    throw BadOptionException();
  }
}

void SmtEngine::setOption(const std::string& key, const SExpr& value)
  throw(BadOptionException, ModalException) {
  Trace("smt") << "SMT setOption(" << key << ", " << value << ")" << endl;

  if(key == ":print-success") {
    throw BadOptionException();
  } else if(key == ":expand-definitions") {
    throw BadOptionException();
  } else if(key == ":interactive-mode") {
    throw BadOptionException();
  } else if(key == ":regular-output-channel") {
    throw BadOptionException();
  } else if(key == ":diagnostic-output-channel") {
    throw BadOptionException();
  } else if(key == ":random-seed") {
    throw BadOptionException();
  } else if(key == ":verbosity") {
    throw BadOptionException();
  } else {
    // The following options can only be set at the beginning; we throw
    // a ModalException if someone tries.
    if(d_logic != "") {
      throw ModalException("logic already set; cannot set options");
    }

    if(key == ":produce-proofs") {
      throw BadOptionException();
    } else if(key == ":produce-unsat-cores") {
      throw BadOptionException();
    } else if(key == ":produce-models") {
      throw BadOptionException();
    } else if(key == ":produce-assignments") {
      throw BadOptionException();
    } else {
      throw BadOptionException();
    }
  }
}

SExpr SmtEngine::getOption(const std::string& key) const
  throw(BadOptionException) {
  Trace("smt") << "SMT getOption(" << key << ")" << endl;
  if(key == ":print-success") {
    return SExpr("true");
  } else if(key == ":expand-definitions") {
    throw BadOptionException();
  } else if(key == ":interactive-mode") {
    throw BadOptionException();
  } else if(key == ":produce-proofs") {
    throw BadOptionException();
  } else if(key == ":produce-unsat-cores") {
    throw BadOptionException();
  } else if(key == ":produce-models") {
    throw BadOptionException();
  } else if(key == ":produce-assignments") {
    throw BadOptionException();
  } else if(key == ":regular-output-channel") {
    return SExpr("stdout");
  } else if(key == ":diagnostic-output-channel") {
    return SExpr("stderr");
  } else if(key == ":random-seed") {
    throw BadOptionException();
  } else if(key == ":verbosity") {
    throw BadOptionException();
  } else {
    throw BadOptionException();
  }
}

void SmtEngine::defineFunction(Expr func,
                               const std::vector<Expr>& formals,
                               Expr formula) {
  Trace("smt") << "SMT defineFunction(" << func << ")" << endl;
  NodeManagerScope nms(d_nodeManager);
  Type formulaType = formula.getType(Options::current()->typeChecking);// type check body
  Type funcType = func.getType();
  Type rangeType = funcType.isFunction() ?
    FunctionType(funcType).getRangeType() : funcType;
  if(formulaType != rangeType) {
    stringstream ss;
    ss << Expr::setlanguage(language::toOutputLanguage(Options::current()->inputLanguage))
       << "Defined function's declared type does not match that of body\n"
       << "The function  : " << func << "\n"
       << "Its range type: " << rangeType << "\n"
       << "The body      : " << formula << "\n"
       << "Body type     : " << formulaType;
    throw TypeCheckingException(func, ss.str());
  }
  TNode funcNode = func.getTNode();
  vector<Node> formalsNodes;
  for(vector<Expr>::const_iterator i = formals.begin(),
        iend = formals.end();
      i != iend;
      ++i) {
    formalsNodes.push_back((*i).getNode());
  }
  TNode formulaNode = formula.getTNode();
  DefinedFunction def(funcNode, formalsNodes, formulaNode);
  // Permit (check-sat) (define-fun ...) (get-value ...) sequences.
  // Otherwise, (check-sat) (get-value ((! foo :named bar))) breaks
  // d_haveAdditions = true;
  d_definedFunctions->insert(funcNode, def);
}

Node SmtEnginePrivate::expandDefinitions(TNode n,
                                         hash_map<TNode, Node, TNodeHashFunction>& cache)
  throw(NoSuchFunctionException, AssertionException) {

  if(n.getKind() != kind::APPLY && n.getNumChildren() == 0) {
    // don't bother putting in the cache
    return n;
  }

  // maybe it's in the cache
  hash_map<TNode, Node, TNodeHashFunction>::iterator cacheHit = cache.find(n);
  if(cacheHit != cache.end()) {
    TNode ret = (*cacheHit).second;
    return ret.isNull() ? n : ret;
  }

  // otherwise expand it
  if(n.getKind() == kind::APPLY) {
    TNode func = n.getOperator();
    SmtEngine::DefinedFunctionMap::const_iterator i =
      d_smt.d_definedFunctions->find(func);
    DefinedFunction def = (*i).second;
    vector<Node> formals = def.getFormals();

    if(Debug.isOn("expand")) {
      Debug("expand") << "found: " << n << endl;
      Debug("expand") << " func: " << func << endl;
      string name = func.getAttribute(expr::VarNameAttr());
      Debug("expand") << "     : \"" << name << "\"" << endl;
    }
    if(i == d_smt.d_definedFunctions->end()) {
      throw NoSuchFunctionException(Expr(d_smt.d_exprManager, new Node(func)));
    }
    if(Debug.isOn("expand")) {
      Debug("expand") << " defn: " << def.getFunction() << endl
                      << "       [";
      if(formals.size() > 0) {
        copy( formals.begin(), formals.end() - 1,
              ostream_iterator<Node>(Debug("expand"), ", ") );
        Debug("expand") << formals.back();
      }
      Debug("expand") << "]" << endl
                      << "       " << def.getFunction().getType() << endl
                      << "       " << def.getFormula() << endl;
    }

    TNode fm = def.getFormula();
    Node instance = fm.substitute(formals.begin(), formals.end(),
                                  n.begin(), n.end());
    Debug("expand") << "made : " << instance << endl;

    Node expanded = this->expandDefinitions(instance, cache);
    cache[n] = (n == expanded ? Node::null() : expanded);
    return expanded;
  } else {
    Debug("expand") << "cons : " << n << endl;
    NodeBuilder<> nb(n.getKind());
    if(n.getMetaKind() == kind::metakind::PARAMETERIZED) {
      Debug("expand") << "op   : " << n.getOperator() << endl;
      nb << n.getOperator();
    }
    for(TNode::iterator i = n.begin(),
          iend = n.end();
        i != iend;
        ++i) {
      Node expanded = this->expandDefinitions(*i, cache);
      Debug("expand") << "exchld: " << expanded << endl;
      nb << expanded;
    }
    Node node = nb;
    cache[n] = n == node ? Node::null() : node;
    return node;
  }
}

Node SmtEnginePrivate::simplify(TNode in, bool noPersist)
  throw(NoSuchFunctionException, AssertionException) {
  try {
    Node n;

    if(!Options::current()->lazyDefinitionExpansion) {
      TimerStat::CodeTimer codeTimer(d_smt.d_definitionExpansionTime);
      Chat() << "Expanding definitions: " << in << endl;
      Debug("expand") << "have: " << n << endl;
      hash_map<TNode, Node, TNodeHashFunction> cache;
      n = this->expandDefinitions(in, cache);
      Debug("expand") << "made: " << n << endl;
    } else {
      n = in;
    }

    if(Options::current()->simplificationStyle == Options::NO_SIMPLIFICATION_STYLE) {
      Chat() << "Not doing nonclausal simplification (by user request)" << endl;
    } else {
      if(Options::current()->simplificationStyle == Options::AGGRESSIVE_SIMPLIFICATION_STYLE) {
        Unimplemented("can't do aggressive nonclausal simplification yet");
      }
      Chat() << "Simplifying (non-clausally): " << n << endl;
      TimerStat::CodeTimer codeTimer(d_smt.d_nonclausalSimplificationTime);
      Trace("smt-simplify") << "simplifying: " << n << endl;
      n = n.substitute(d_topLevelSubstitutions.begin(), d_topLevelSubstitutions.end());
      size_t oldSize = d_topLevelSubstitutions.size();
      n = d_smt.d_theoryEngine->simplify(n, d_topLevelSubstitutions);
      if(n.getKind() != kind::AND && d_topLevelSubstitutions.size() > oldSize) {
        Debug("smt-simplify") << "new top level substitutions not incorporated "
                              << "into assertion ("
                              << (d_topLevelSubstitutions.size() - oldSize)
                              << "):" << endl;
        NodeBuilder<> b(kind::AND);
        b << n;
        for(size_t i = oldSize; i < d_topLevelSubstitutions.size(); ++i) {
          Debug("smt-simplify") << "  " << d_topLevelSubstitutions[i] << endl;
          TNode x = d_topLevelSubstitutions[i].first;
          TNode y = d_topLevelSubstitutions[i].second;
          if(x.getType().isBoolean()) {
            if(x.getMetaKind() == kind::metakind::CONSTANT) {
              if(y.getMetaKind() == kind::metakind::CONSTANT) {
                if(x == y) {
                  b << d_smt.d_nodeManager->mkConst(true);
                } else {
                  b << d_smt.d_nodeManager->mkConst(false);
                }
              } else {
                if(x.getConst<bool>()) {
                  b << y;
                } else {
                  b << BooleanSimplification::negate(y);
                }
              }
            } else if(y.getMetaKind() == kind::metakind::CONSTANT) {
              if(y.getConst<bool>()) {
                b << x;
              } else {
                b << BooleanSimplification::negate(x);
              }
            } else {
              b << x.iffNode(y);
            }
          } else {
            b << x.eqNode(y);
          }
        }
        n = b;
        n = BooleanSimplification::simplifyConflict(n);
      }
      Trace("smt-simplify") << "+++++++ got: " << n << endl;
      if(noPersist) {
        d_topLevelSubstitutions.resize(oldSize);
      }
    }

    // For now, don't re-statically-learn from learned facts; this could
    // be useful though (e.g., theory T1 could learn something further
    // from something learned previously by T2).
    Chat() << "Performing static learning: " << n << endl;
    TimerStat::CodeTimer codeTimer(d_smt.d_staticLearningTime);
    NodeBuilder<> learned(kind::AND);
    learned << n;
    d_smt.d_theoryEngine->staticLearning(n, learned);
    if(learned.getNumChildren() == 1) {
      learned.clear();
    } else {
      n = learned;
    }

    return n;

  } catch(TypeCheckingExceptionPrivate& tcep) {
    // Calls to this function should have already weeded out any
    // typechecking exceptions via (e.g.) ensureBoolean().  But a
    // theory could still create a new expression that isn't
    // well-typed, and we don't want the C++ runtime to abort our
    // process without any error notice.
    stringstream ss;
    ss << Expr::setlanguage(language::toOutputLanguage(Options::current()->inputLanguage))
       << "A bad expression was produced.  Original exception follows:\n"
       << tcep;
    InternalError(ss.str().c_str());
  }
}

Node SmtEnginePrivate::preprocess(TNode in) throw(AssertionException) {
  try {
    Chat() << "Preprocessing / rewriting: " << in << endl;
    return d_smt.d_theoryEngine->preprocess(in);
  } catch(TypeCheckingExceptionPrivate& tcep) {
    // Calls to this function should have already weeded out any
    // typechecking exceptions via (e.g.) ensureBoolean().  But a
    // theory could still create a new expression that isn't
    // well-typed, and we don't want the C++ runtime to abort our
    // process without any error notice.
    stringstream ss;
    ss << Expr::setlanguage(language::toOutputLanguage(Options::current()->inputLanguage))
       << "A bad expression was produced.  Original exception follows:\n"
       << tcep;
    InternalError(ss.str().c_str());
  }
}

Result SmtEngine::check() {
  Trace("smt") << "SMT check()" << endl;

  // make sure the prop layer has all assertions
  d_private->pushAssertions();

  return d_propEngine->checkSat();
}

Result SmtEngine::quickCheck() {
  Trace("smt") << "SMT quickCheck()" << endl;
  return Result(Result::VALIDITY_UNKNOWN, Result::REQUIRES_FULL_CHECK);
}

void SmtEnginePrivate::adjustAssertions(bool purge) {

  // If the "purge" argument is true, we ignore the mode and push all
  // assertions out to the propositional layer (by pretending we're in
  // INCREMENTAL mode).

  Options::SimplificationMode mode =
    purge ? Options::INCREMENTAL_MODE : Options::current()->simplificationMode;

  Trace("smt") << "SMT processing assertion lists in " << mode << " mode" << endl;

  if(mode == Options::BATCH_MODE) {
    // nothing to do in batch mode until pushAssertions() is called
  } else if(mode == Options::INCREMENTAL_LAZY_SAT_MODE ||
            mode == Options::INCREMENTAL_MODE) {
    // make sure d_assertionsToSimplify is cleared out, and everything
    // is on d_assertionsToPushToSat

    for(vector<Node>::iterator i = d_assertionsToSimplify.begin(),
          i_end = d_assertionsToSimplify.end();
        i != i_end;
        ++i) {
      Trace("smt") << "SMT simplifying " << *i << endl;
      d_assertionsToPushToSat.push_back(this->simplify(*i));
    }
    d_assertionsToSimplify.clear();

    if(mode == Options::INCREMENTAL_MODE) {
      // make sure the d_assertionsToPushToSat queue is also cleared out

      for(vector<Node>::iterator i = d_assertionsToPushToSat.begin(),
            i_end = d_assertionsToPushToSat.end();
          i != i_end;
          ++i) {
        Trace("smt") << "SMT preprocessing " << *i << endl;
        Node n = this->preprocess(*i);
        Trace("smt") << "SMT pushing to MiniSat " << n << endl;

        Chat() << "Pushing to MiniSat: " << n << endl;
        d_smt.d_propEngine->assertFormula(n);
      }
      d_assertionsToPushToSat.clear();
    }
  } else {
    Unhandled(mode);
  }
}

void SmtEnginePrivate::addFormula(TNode n)
  throw(NoSuchFunctionException, AssertionException) {

  Trace("smt") << "push_back assertion " << n << endl;
  d_smt.d_haveAdditions = true;

  d_assertionsToSimplify.push_back(n);
  adjustAssertions();
}

void SmtEngine::ensureBoolean(const BoolExpr& e) {
  Type type = e.getType(Options::current()->typeChecking);
  Type boolType = d_exprManager->booleanType();
  if(type != boolType) {
    stringstream ss;
    ss << Expr::setlanguage(language::toOutputLanguage(Options::current()->inputLanguage))
       << "Expected " << boolType << "\n"
       << "The assertion : " << e << "\n"
       << "Its type      : " << type;
    throw TypeCheckingException(e, ss.str());
  }
}

Result SmtEngine::checkSat(const BoolExpr& e) {
  Assert(e.getExprManager() == d_exprManager);
  NodeManagerScope nms(d_nodeManager);
  Trace("smt") << "SMT checkSat(" << e << ")" << endl;
  if(d_queryMade && !Options::current()->incrementalSolving) {
    throw ModalException("Cannot make multiple queries unless "
                         "incremental solving is enabled "
                         "(try --incremental)");
  }
  d_queryMade = true;
  ensureBoolean(e);// ensure expr is type-checked at this point
  internalPush();
  d_private->addFormula(e.getNode());
  Result r = check().asSatisfiabilityResult();
  internalPop();
  d_status = r;
  d_haveAdditions = false;
  Trace("smt") << "SMT checkSat(" << e << ") ==> " << r << endl;
  return r;
}

Result SmtEngine::query(const BoolExpr& e) {
  Assert(e.getExprManager() == d_exprManager);
  NodeManagerScope nms(d_nodeManager);
  Trace("smt") << "SMT query(" << e << ")" << endl;
  if(d_queryMade && !Options::current()->incrementalSolving) {
    throw ModalException("Cannot make multiple queries unless "
                         "incremental solving is enabled "
                         "(try --incremental)");
  }
  d_queryMade = true;
  ensureBoolean(e);// ensure expr is type-checked at this point
  internalPush();
  d_private->addFormula(e.getNode().notNode());
  Result r = check().asValidityResult();
  internalPop();
  d_status = r;
  d_haveAdditions = false;
  Trace("smt") << "SMT query(" << e << ") ==> " << r << endl;
  return r;
}

Result SmtEngine::assertFormula(const BoolExpr& e) {
  Assert(e.getExprManager() == d_exprManager);
  NodeManagerScope nms(d_nodeManager);
  Trace("smt") << "SMT assertFormula(" << e << ")" << endl;
  ensureBoolean(e);// type check node
  if(d_assertionList != NULL) {
    d_assertionList->push_back(e);
  }
  d_private->addFormula(e.getNode());
  return quickCheck().asValidityResult();
}

Expr SmtEngine::simplify(const Expr& e) {
  Assert(e.getExprManager() == d_exprManager);
  NodeManagerScope nms(d_nodeManager);
  if( Options::current()->typeChecking ) {
    e.getType(true);// ensure expr is type-checked at this point
  }
  Trace("smt") << "SMT simplify(" << e << ")" << endl;
  return BooleanSimplification::simplify(d_private->simplify(e, true)).toExpr();
}

Expr SmtEngine::getValue(const Expr& e)
  throw(ModalException, AssertionException) {
  Assert(e.getExprManager() == d_exprManager);
  NodeManagerScope nms(d_nodeManager);
  Type type = e.getType(Options::current()->typeChecking);// ensure expr is type-checked at this point
  Trace("smt") << "SMT getValue(" << e << ")" << endl;
  if(!Options::current()->produceModels) {
    const char* msg =
      "Cannot get value when produce-models options is off.";
    throw ModalException(msg);
  }
  if(d_status.isNull() ||
     d_status.asSatisfiabilityResult() != Result::SAT ||
     d_haveAdditions) {
    const char* msg =
      "Cannot get value unless immediately proceded by SAT/INVALID response.";
    throw ModalException(msg);
  }
  if(type.isFunction() || type.isPredicate() ||
     type.isKind() || type.isSortConstructor()) {
    const char* msg =
      "Cannot get value of a function, predicate, or sort.";
    throw ModalException(msg);
  }

  Node eNode = e.getNode();
  Node n = d_private->preprocess(eNode);// theory rewriting

  Trace("smt") << "--- getting value of " << n << endl;
  Node resultNode = d_theoryEngine->getValue(n);

  // type-check the result we got
  Assert(resultNode.isNull() || resultNode.getType() == eNode.getType());
  return Expr(d_exprManager, new Node(resultNode));
}

bool SmtEngine::addToAssignment(const Expr& e) throw(AssertionException) {
  NodeManagerScope nms(d_nodeManager);
  Type type = e.getType(Options::current()->typeChecking);
  // must be Boolean
  CheckArgument( type.isBoolean(), e,
                 "expected Boolean-typed variable or function application "
                 "in addToAssignment()" );
  Node n = e.getNode();
  // must be an APPLY of a zero-ary defined function, or a variable
  CheckArgument( ( ( n.getKind() == kind::APPLY &&
                     ( d_definedFunctions->find(n.getOperator()) !=
                       d_definedFunctions->end() ) &&
                     n.getNumChildren() == 0 ) ||
                   n.getMetaKind() == kind::metakind::VARIABLE ), e,
                 "expected variable or defined-function application "
                 "in addToAssignment(),\ngot %s", e.toString().c_str() );
  if(!Options::current()->produceAssignments) {
    return false;
  }
  if(d_assignments == NULL) {
    d_assignments = new(true) AssignmentSet(d_context);
  }
  d_assignments->insert(n);

  return true;
}

SExpr SmtEngine::getAssignment() throw(ModalException, AssertionException) {
  Trace("smt") << "SMT getAssignment()" << endl;
  if(!Options::current()->produceAssignments) {
    const char* msg =
      "Cannot get the current assignment when "
      "produce-assignments option is off.";
    throw ModalException(msg);
  }
  if(d_status.isNull() ||
     d_status.asSatisfiabilityResult() != Result::SAT ||
     d_haveAdditions) {
    const char* msg =
      "Cannot get value unless immediately proceded by SAT/INVALID response.";
    throw ModalException(msg);
  }

  if(d_assignments == NULL) {
    return SExpr();
  }

  NodeManagerScope nms(d_nodeManager);
  vector<SExpr> sexprs;
  TypeNode boolType = d_nodeManager->booleanType();
  for(AssignmentSet::const_iterator i = d_assignments->begin(),
        iend = d_assignments->end();
      i != iend;
      ++i) {
    Assert((*i).getType() == boolType);

    Node n = d_private->preprocess(*i);// theory rewriting

    Trace("smt") << "--- getting value of " << n << endl;
    Node resultNode = d_theoryEngine->getValue(n);

    // type-check the result we got
    Assert(resultNode.isNull() || resultNode.getType() == boolType);

    vector<SExpr> v;
    if((*i).getKind() == kind::APPLY) {
      Assert((*i).getNumChildren() == 0);
      v.push_back((*i).getOperator().toString());
    } else {
      Assert((*i).getMetaKind() == kind::metakind::VARIABLE);
      v.push_back((*i).toString());
    }
    v.push_back(resultNode.toString());
    sexprs.push_back(v);
  }
  return SExpr(sexprs);
}

vector<Expr> SmtEngine::getAssertions()
  throw(ModalException, AssertionException) {
  NodeManagerScope nms(d_nodeManager);
  Trace("smt") << "SMT getAssertions()" << endl;
  if(!Options::current()->interactive) {
    const char* msg =
      "Cannot query the current assertion list when not in interactive mode.";
    throw ModalException(msg);
  }
  Assert(d_assertionList != NULL);
  return vector<Expr>(d_assertionList->begin(), d_assertionList->end());
}

void SmtEngine::push() {
  NodeManagerScope nms(d_nodeManager);
  Trace("smt") << "SMT push()" << endl;
  if(!Options::current()->incrementalSolving) {
    throw ModalException("Cannot push when not solving incrementally (use --incremental)");
  }
  d_userLevels.push_back(d_userContext->getLevel());
  internalPush();
  Debug("userpushpop") << "SmtEngine: pushed to level "
                       << d_userContext->getLevel() << endl;
}

void SmtEngine::pop() {
  NodeManagerScope nms(d_nodeManager);
  Trace("smt") << "SMT pop()" << endl;
  if(!Options::current()->incrementalSolving) {
    throw ModalException("Cannot pop when not solving incrementally (use --incremental)");
  }
  AlwaysAssert(d_userLevels.size() > 0 && d_userLevels.back() < d_userContext->getLevel());
  while (d_userLevels.back() < d_userContext->getLevel()) {
    internalPop();
  }
  d_userLevels.pop_back();

  Debug("userpushpop") << "SmtEngine: popped to level "
                       << d_userContext->getLevel() << endl;
  // FIXME: should we reset d_status here?
  // SMT-LIBv2 spec seems to imply no, but it would make sense to..
}

void SmtEngine::internalPop() {
  Trace("smt") << "internalPop()" << endl;
  d_propEngine->pop();
  d_userContext->pop();
}

void SmtEngine::internalPush() {
  Trace("smt") << "internalPush()" << endl;
  d_userContext->push();
  d_propEngine->push();
}

StatisticsRegistry* SmtEngine::getStatisticsRegistry() const {
  return d_exprManager->d_nodeManager->getStatisticsRegistry();
}

}/* CVC4 namespace */
