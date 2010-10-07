/*********************                                                        */
/*! \file smt_engine.cpp
 ** \verbatim
 ** Original author: mdeters
 ** Major contributors: dejan
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief The main entry point into the CVC4 library's SMT interface.
 **
 ** The main entry point into the CVC4 library's SMT interface.
 **/

#include <vector>
#include <string>

#include "smt/smt_engine.h"
#include "smt/modal_exception.h"
#include "smt/bad_option_exception.h"
#include "smt/no_such_function_exception.h"
#include "context/context.h"
#include "context/cdlist.h"
#include "expr/expr.h"
#include "expr/command.h"
#include "expr/node_builder.h"
#include "util/output.h"
#include "util/exception.h"
#include "util/options.h"
#include "prop/prop_engine.h"
#include "theory/theory_engine.h"

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
public:

  /**
   * Pre-process an Node.  This is expected to be highly-variable,
   * with a lot of "source-level configurability" to add multiple
   * passes over the Node.  TODO: may need to specify a LEVEL of
   * preprocessing (certain contexts need more/less ?).
   */
  static Node preprocess(SmtEngine& smt, TNode n)
    throw(NoSuchFunctionException, AssertionException);

  /**
   * Adds a formula to the current context.
   */
  static void addFormula(SmtEngine& smt, TNode n)
    throw(NoSuchFunctionException, AssertionException);

  /**
   * Expand definitions in n.
   */
  static Node expandDefinitions(SmtEngine& smt, TNode n)
    throw(NoSuchFunctionException, AssertionException);
};/* class SmtEnginePrivate */

}/* namespace CVC4::smt */

using namespace CVC4::smt;

SmtEngine::SmtEngine(ExprManager* em, const Options* opts) throw() :
  d_context(em->getContext()),
  d_exprManager(em),
  d_nodeManager(em->getNodeManager()),
  d_options(opts),
  /* These next few are initialized below, after we have a NodeManager
   * in scope. */
  d_decisionEngine(NULL),
  d_theoryEngine(NULL),
  d_propEngine(NULL),
  d_assertionList(NULL) {

  NodeManagerScope nms(d_nodeManager);

  d_decisionEngine = new DecisionEngine;
  // We have mutual dependancy here, so we add the prop engine to the theory
  // engine later (it is non-essential there)
  d_theoryEngine = new TheoryEngine(d_context, opts);
  d_propEngine = new PropEngine(opts, d_decisionEngine,
                                d_theoryEngine, d_context);
  d_theoryEngine->setPropEngine(d_propEngine);

  d_definedFunctions = new(true) DefinedFunctionMap(d_context);

  if(d_options->interactive) {
    d_assertionList = new(true) AssertionList(d_context);
  }
}

void SmtEngine::shutdown() {
  d_propEngine->shutdown();
  d_theoryEngine->shutdown();
  d_decisionEngine->shutdown();
}

SmtEngine::~SmtEngine() {
  NodeManagerScope nms(d_nodeManager);

  shutdown();

  if(d_assertionList != NULL) {
    d_assertionList->deleteSelf();
  }

  d_definedFunctions->deleteSelf();

  delete d_theoryEngine;
  delete d_propEngine;
  delete d_decisionEngine;
}

void SmtEngine::setInfo(const string& key, const SExpr& value)
  throw(BadOptionException) {
  if(key == ":status") {
    return;
  }
  // FIXME implement me
  throw BadOptionException();
}

const SExpr& SmtEngine::getInfo(const string& key) const
  throw(BadOptionException) {
  // FIXME implement me
  throw BadOptionException();
}

void SmtEngine::setOption(const string& key, const SExpr& value)
  throw(BadOptionException) {
  // FIXME implement me
  throw BadOptionException();
}

const SExpr& SmtEngine::getOption(const string& key) const
  throw(BadOptionException) {
  // FIXME implement me
  throw BadOptionException();
}

void SmtEngine::defineFunction(Expr func,
                               const vector<Expr>& formals,
                               Expr formula) {
  NodeManagerScope nms(d_nodeManager);
  Type formulaType = formula.getType(true);// type check body
  if(formulaType != FunctionType(func.getType()).getRangeType()) {
    stringstream ss;
    ss << "Defined function's declared type does not match type of body\n"
       << "The function: " << func << "\n"
       << "Its type    : " << func.getType() << "\n"
       << "The body    : " << formula << "\n"
       << "Body type   : " << formulaType << "\n";
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
  d_definedFunctions->insert(funcNode, def);
}

Node SmtEnginePrivate::expandDefinitions(SmtEngine& smt, TNode n)
  throw(NoSuchFunctionException, AssertionException) {
  if(n.getKind() == kind::APPLY) {
    TNode func = n.getOperator();
    SmtEngine::DefinedFunctionMap::const_iterator i =
      smt.d_definedFunctions->find(func);
    DefinedFunction def = (*i).second;
    vector<Node> formals = def.getFormals();

    if(Debug.isOn("expand")) {
      Debug("expand") << "found: " << n << endl;
      Debug("expand") << " func: " << func << endl;
      string name = func.getAttribute(expr::VarNameAttr());
      Debug("expand") << "     : \"" << name << "\"" << endl;
      if(i == smt.d_definedFunctions->end()) {
        throw NoSuchFunctionException(Expr(smt.d_exprManager, new Node(func)));
      }
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

    Node expanded = expandDefinitions(smt, instance);
    return expanded;
  } else if(n.getNumChildren() == 0) {
    return n;
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
      Node expanded = expandDefinitions(smt, *i);
      Debug("expand") << "exchld: " << expanded << endl;
      nb << expanded;
    }
    Node node = nb;
    return node;
  }
}

Node SmtEnginePrivate::preprocess(SmtEngine& smt, TNode n)
  throw(NoSuchFunctionException, AssertionException) {
  if(!smt.d_options->lazyDefinitionExpansion) {
    Node node = expandDefinitions(smt, n);
    Debug("expand") << "have: " << n << endl
                    << "made: " << node << endl;
    return smt.d_theoryEngine->preprocess(node);
  } else {
    return smt.d_theoryEngine->preprocess(n);
  }
}

Result SmtEngine::check() {
  Debug("smt") << "SMT check()" << endl;
  return d_propEngine->checkSat();
}

Result SmtEngine::quickCheck() {
  Debug("smt") << "SMT quickCheck()" << endl;
  return Result(Result::VALIDITY_UNKNOWN);
}

void SmtEnginePrivate::addFormula(SmtEngine& smt, TNode n)
  throw(NoSuchFunctionException, AssertionException) {
  Debug("smt") << "push_back assertion " << n << endl;
  smt.d_propEngine->assertFormula(SmtEnginePrivate::preprocess(smt, n));
}

Result SmtEngine::checkSat(const BoolExpr& e) {
  NodeManagerScope nms(d_nodeManager);
  Debug("smt") << "SMT checkSat(" << e << ")" << endl;
  SmtEnginePrivate::addFormula(*this, e.getNode());
  Result r = check().asSatisfiabilityResult();
  Debug("smt") << "SMT checkSat(" << e << ") ==> " << r << endl;
  return r;
}

Result SmtEngine::query(const BoolExpr& e) {
  NodeManagerScope nms(d_nodeManager);
  Debug("smt") << "SMT query(" << e << ")" << endl;
  SmtEnginePrivate::addFormula(*this, e.getNode().notNode());
  Result r = check().asValidityResult();
  Debug("smt") << "SMT query(" << e << ") ==> " << r << endl;
  return r;
}

Result SmtEngine::assertFormula(const BoolExpr& e) {
  NodeManagerScope nms(d_nodeManager);
  Debug("smt") << "SMT assertFormula(" << e << ")" << endl;
  SmtEnginePrivate::addFormula(*this, e.getNode());
  return quickCheck().asValidityResult();
}

Expr SmtEngine::simplify(const Expr& e) {
  NodeManagerScope nms(d_nodeManager);
  Debug("smt") << "SMT simplify(" << e << ")" << endl;
  Unimplemented();
}

Expr SmtEngine::getValue(Expr term)
  throw(ModalException, AssertionException) {
  if(!d_options->interactive) {
    const char* msg =
      "Cannot get value when not in interactive mode.";
    throw ModalException(msg);
  }
  if(!d_options->produceModels) {
    const char* msg =
      "Cannot get value when produce-models options is off.";
    throw ModalException(msg);
  }
  // TODO also check that the last query was sat/unknown, without intervening
  // assertions

  NodeManagerScope nms(d_nodeManager);

  Unimplemented();
}

SExpr SmtEngine::getAssignment() throw(ModalException, AssertionException) {
  if(!d_options->produceAssignments) {
    const char* msg =
      "Cannot get the current assignment when produce-assignments option is off.";
    throw ModalException(msg);
  }
  // TODO also check that the last query was sat/unknown, without intervening
  // assertions

  NodeManagerScope nms(d_nodeManager);

  Unimplemented();
}

vector<Expr> SmtEngine::getAssertions() throw(ModalException, AssertionException) {
  if(!d_options->interactive) {
    const char* msg =
      "Cannot query the current assertion list when not in interactive mode.";
    throw ModalException(msg);
  }
  Assert(d_assertionList != NULL);
  return vector<Expr>(d_assertionList->begin(), d_assertionList->end());
}

void SmtEngine::push() {
  NodeManagerScope nms(d_nodeManager);
  Debug("smt") << "SMT push()" << endl;
  Unimplemented();
}

void SmtEngine::pop() {
  NodeManagerScope nms(d_nodeManager);
  Debug("smt") << "SMT pop()" << endl;
  Unimplemented();
}

}/* CVC4 namespace */
