/*********************                                                        */
/*! \file expr_template.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Morgan Deters, Dejan Jovanovic, Tim King
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Public-facing expression interface, implementation.
 **
 ** Public-facing expression interface, implementation.
 **/
#include "expr/expr.h"

#include <iostream>
#include <iterator>
#include <utility>
#include <vector>

#include "base/cvc4_assert.h"
#include "expr/expr_manager_scope.h"
#include "expr/node.h"
#include "expr/node_algorithm.h"
#include "expr/node_manager_attributes.h"
#include "expr/variable_type_map.h"

${includes}

// This is a hack, but an important one: if there's an error, the
// compiler directs the user to the template file instead of the
// generated one.  We don't want the user to modify the generated one,
// since it'll get overwritten on a later build.
#line 37 "${template}"

using namespace CVC4::kind;
using namespace std;

namespace CVC4 {

class ExprManager;

std::ostream& operator<<(std::ostream& out, const TypeCheckingException& e) {
  return out << e.getMessage() << ": " << e.getExpression();
}

std::ostream& operator<<(std::ostream& out, const Expr& e) {
  if(e.isNull()) {
    return out << "null";
  } else {
    ExprManagerScope ems(*e.getExprManager());
    return out << e.getNode();
  }
}

std::ostream& operator<<(std::ostream& out, const std::vector<Expr>& container)
{
  container_to_stream(out, container);
  return out;
}

std::ostream& operator<<(std::ostream& out, const std::set<Expr>& container)
{
  container_to_stream(out, container);
  return out;
}

std::ostream& operator<<(
    std::ostream& out,
    const std::unordered_set<Expr, ExprHashFunction>& container)
{
  container_to_stream(out, container);
  return out;
}

template <typename V>
std::ostream& operator<<(std::ostream& out, const std::map<Expr, V>& container)
{
  container_to_stream(out, container);
  return out;
}

template <typename V>
std::ostream& operator<<(
    std::ostream& out,
    const std::unordered_map<Expr, V, ExprHashFunction>& container)
{
  container_to_stream(out, container);
  return out;
}

TypeCheckingException::TypeCheckingException(const TypeCheckingException& t)
    : Exception(t.d_msg), d_expr(new Expr(t.getExpression()))
{
}

TypeCheckingException::TypeCheckingException(const Expr& expr,
                                             std::string message)
    : Exception(message), d_expr(new Expr(expr))
{
}

TypeCheckingException::TypeCheckingException(
    ExprManager* em, const TypeCheckingExceptionPrivate* exc)
    : Exception(exc->getMessage()),
      d_expr(new Expr(em, new Node(exc->getNode())))
{
}

TypeCheckingException::~TypeCheckingException() { delete d_expr; }

void TypeCheckingException::toStream(std::ostream& os) const
{
  os << "Error during type checking: " << d_msg << endl
     << "The ill-typed expression: " << *d_expr;
}

Expr TypeCheckingException::getExpression() const { return *d_expr; }

Expr::Expr() :
  d_node(new Node),
  d_exprManager(NULL) {
  // We do not need to wrap this in an ExprManagerScope as `new Node` is backed
  // by NodeValue::null which is a static outside of a NodeManager.
}

Expr::Expr(ExprManager* em, Node* node) :
  d_node(node),
  d_exprManager(em) {
  // We do not need to wrap this in an ExprManagerScope as this only initializes
  // pointers
}

Expr::Expr(const Expr& e) :
  d_node(NULL),
  d_exprManager(e.d_exprManager) {
  ExprManagerScope ems(*this);
  d_node = new Node(*e.d_node);
}

Expr::~Expr() {
  ExprManagerScope ems(*this);
  delete d_node;
}

ExprManager* Expr::getExprManager() const {
  return d_exprManager;
}

namespace expr {

static Node exportConstant(TNode n, NodeManager* to, ExprManagerMapCollection& vmap);

class ExportPrivate {
private:
  typedef std::unordered_map <NodeTemplate<false>, NodeTemplate<true>, TNodeHashFunction> ExportCache;
  ExprManager* from;
  ExprManager* to;
  ExprManagerMapCollection& vmap;
  uint32_t flags;
  ExportCache exportCache;
public:
  ExportPrivate(ExprManager* from, ExprManager* to, ExprManagerMapCollection& vmap, uint32_t flags) : from(from), to(to), vmap(vmap), flags(flags) {}
  Node exportInternal(TNode n) {

    if(n.isNull()) return Node::null();
    if(theory::kindToTheoryId(n.getKind()) == theory::THEORY_DATATYPES) {
      throw ExportUnsupportedException
        ("export of node belonging to theory of DATATYPES kinds unsupported");
    }

    if(n.getMetaKind() == metakind::CONSTANT) {
      if(n.getKind() == kind::EMPTYSET) {
        Type type = from->exportType(n.getConst< ::CVC4::EmptySet >().getType(), to, vmap);
        return to->mkConst(::CVC4::EmptySet(type));
      }
      return exportConstant(n, NodeManager::fromExprManager(to), vmap);
    } else if(n.getMetaKind() == metakind::NULLARY_OPERATOR ){
      Expr from_e(from, new Node(n));
      Type type = from->exportType(from_e.getType(), to, vmap);
      return to->mkNullaryOperator(type, n.getKind()); // FIXME thread safety
    } else if(n.getMetaKind() == metakind::VARIABLE) {
      Expr from_e(from, new Node(n));
      Expr& to_e = vmap.d_typeMap[from_e];
      if(! to_e.isNull()) {
        Debug("export") << "+ mapped `" << from_e << "' to `" << to_e << "'" << std::endl;
        return to_e.getNode();
      } else {
        // construct new variable in other manager:
        // to_e is a ref, so this inserts from_e -> to_e
        std::string name;
        Type type = from->exportType(from_e.getType(), to, vmap);
        if(Node::fromExpr(from_e).getAttribute(VarNameAttr(), name)) {
          if (n.getKind() == kind::BOUND_VARIABLE)
          {
            // bound vars are only available at the Node level (not the Expr
            // level)
            TypeNode typeNode = TypeNode::fromType(type);
            NodeManager* to_nm = NodeManager::fromExprManager(to);
            Node n = to_nm->mkBoundVar(name, typeNode);  // FIXME thread safety

            // Make sure that the correct `NodeManager` is in scope while
            // converting the node to an expression.
            NodeManagerScope to_nms(to_nm);
            to_e = n.toExpr();
          } else if(n.getKind() == kind::VARIABLE) {
            bool isGlobal;
            Node::fromExpr(from_e).getAttribute(GlobalVarAttr(), isGlobal);

            // Temporarily set the node manager to nullptr; this gets around
            // a check that mkVar isn't called internally
            NodeManagerScope nullScope(nullptr);
            to_e = to->mkVar(name, type, isGlobal ? ExprManager::VAR_FLAG_GLOBAL : flags);// FIXME thread safety
          } else if(n.getKind() == kind::SKOLEM) {
            // skolems are only available at the Node level (not the Expr level)
            TypeNode typeNode = TypeNode::fromType(type);
            NodeManager* to_nm = NodeManager::fromExprManager(to);
            Node n = to_nm->mkSkolem(name, typeNode, "is a skolem variable imported from another ExprManager");// FIXME thread safety

            // Make sure that the correct `NodeManager` is in scope while
            // converting the node to an expression.
            NodeManagerScope to_nms(to_nm);
            to_e = n.toExpr();
          } else {
            Unhandled();
          }

          Debug("export") << "+ exported var `" << from_e << "'[" << from_e.getId() << "] with name `" << name << "' and type `" << from_e.getType() << "' to `" << to_e << "'[" << to_e.getId() << "] with type `" << type << "'" << std::endl;
        } else {
          if (n.getKind() == kind::BOUND_VARIABLE)
          {
            // bound vars are only available at the Node level (not the Expr
            // level)
            TypeNode typeNode = TypeNode::fromType(type);
            NodeManager* to_nm = NodeManager::fromExprManager(to);
            Node n = to_nm->mkBoundVar(typeNode);  // FIXME thread safety

            // Make sure that the correct `NodeManager` is in scope while
            // converting the node to an expression.
            NodeManagerScope to_nms(to_nm);
            to_e = n.toExpr();
          }
          else
          {
            // Temporarily set the node manager to nullptr; this gets around
            // a check that mkVar isn't called internally
            NodeManagerScope nullScope(nullptr);
            to_e = to->mkVar(type);  // FIXME thread safety
          }
          Debug("export") << "+ exported unnamed var `" << from_e << "' with type `" << from_e.getType() << "' to `" << to_e << "' with type `" << type << "'" << std::endl;
        }
        uint64_t to_int = (uint64_t)(to_e.getNode().d_nv);
        uint64_t from_int = (uint64_t)(from_e.getNode().d_nv);
        vmap.d_from[to_int] = from_int;
        vmap.d_to[from_int] = to_int;
        vmap.d_typeMap[to_e] = from_e;// insert other direction too

        // Make sure that the expressions are associated with the correct
        // `ExprManager`s.
        Assert(from_e.getExprManager() == from);
        Assert(to_e.getExprManager() == to);
        return Node::fromExpr(to_e);
      }
    } else {
      if(exportCache.find(n) != exportCache.end()) {
        return exportCache[n];
      }

      std::vector<Node> children;
      Debug("export") << "n: " << n << std::endl;
      if(n.getMetaKind() == kind::metakind::PARAMETERIZED) {
        Debug("export") << "+ parameterized, op is " << n.getOperator() << std::endl;
        children.reserve(n.getNumChildren() + 1);
        children.push_back(exportInternal(n.getOperator()));
      } else {
        children.reserve(n.getNumChildren());
      }
      for(TNode::iterator i = n.begin(), i_end = n.end(); i != i_end; ++i) {
        Debug("export") << "+ child: " << *i << std::endl;
        children.push_back(exportInternal(*i));
      }
      if(Debug.isOn("export")) {
        Debug("export") << "children for export from " << n << std::endl;

        // `n` belongs to the `from` ExprManager, so begin ExprManagerScope
        // after printing `n`
        ExprManagerScope ems(*to);
        for(std::vector<Node>::iterator i = children.begin(), i_end = children.end(); i != i_end; ++i) {
          Debug("export") << "  child: " << *i << std::endl;
        }
      }

      // FIXME thread safety
      Node ret = NodeManager::fromExprManager(to)->mkNode(n.getKind(), children);

      exportCache[n] = ret;
      return ret;
    }
  }/* exportInternal() */

};

}/* CVC4::expr namespace */

Expr Expr::exportTo(ExprManager* exprManager, ExprManagerMapCollection& variableMap,
                    uint32_t flags /* = 0 */) const {
  Assert(d_exprManager != exprManager,
         "No sense in cloning an Expr in the same ExprManager");
  ExprManagerScope ems(*this);
  return Expr(exprManager, new Node(expr::ExportPrivate(d_exprManager, exprManager, variableMap, flags).exportInternal(*d_node)));
}

Expr& Expr::operator=(const Expr& e) {
  Assert(d_node != NULL, "Unexpected NULL expression pointer!");
  Assert(e.d_node != NULL, "Unexpected NULL expression pointer!");

  if(this != &e) {
    if(d_exprManager == e.d_exprManager) {
      ExprManagerScope ems(*this);
      *d_node = *e.d_node;
    } else {
      // This happens more than you think---every time you set to or
      // from the null Expr.  It's tricky because each node manager
      // must be in play at the right time.

      ExprManagerScope ems1(*this);
      *d_node = Node::null();

      ExprManagerScope ems2(e);
      *d_node = *e.d_node;

      d_exprManager = e.d_exprManager;
    }
  }
  return *this;
}

bool Expr::operator==(const Expr& e) const {
  if(d_exprManager != e.d_exprManager) {
    return false;
  }
  ExprManagerScope ems(*this);
  Assert(d_node != NULL, "Unexpected NULL expression pointer!");
  Assert(e.d_node != NULL, "Unexpected NULL expression pointer!");
  return *d_node == *e.d_node;
}

bool Expr::operator!=(const Expr& e) const {
  return !(*this == e);
}

bool Expr::operator<(const Expr& e) const {
  Assert(d_node != NULL, "Unexpected NULL expression pointer!");
  Assert(e.d_node != NULL, "Unexpected NULL expression pointer!");
  if(isNull() && !e.isNull()) {
    return true;
  }
  ExprManagerScope ems(*this);
  return *d_node < *e.d_node;
}

bool Expr::operator>(const Expr& e) const {
  Assert(d_node != NULL, "Unexpected NULL expression pointer!");
  Assert(e.d_node != NULL, "Unexpected NULL expression pointer!");
  if(isNull() && !e.isNull()) {
    return true;
  }
  ExprManagerScope ems(*this);
  return *d_node > *e.d_node;
}

uint64_t Expr::getId() const
{
  ExprManagerScope ems(*this);
  Assert(d_node != NULL, "Unexpected NULL expression pointer!");
  return d_node->getId();
}

Kind Expr::getKind() const {
  ExprManagerScope ems(*this);
  Assert(d_node != NULL, "Unexpected NULL expression pointer!");
  return d_node->getKind();
}

size_t Expr::getNumChildren() const {
  ExprManagerScope ems(*this);
  Assert(d_node != NULL, "Unexpected NULL expression pointer!");
  return d_node->getNumChildren();
}

Expr Expr::operator[](unsigned i) const {
  ExprManagerScope ems(*this);
  Assert(d_node != NULL, "Unexpected NULL expression pointer!");
  Assert(i >= 0 && i < d_node->getNumChildren(), "Child index out of bounds");
  return Expr(d_exprManager, new Node((*d_node)[i]));
}

bool Expr::hasOperator() const {
  ExprManagerScope ems(*this);
  Assert(d_node != NULL, "Unexpected NULL expression pointer!");
  return d_node->hasOperator();
}

Expr Expr::getOperator() const {
  ExprManagerScope ems(*this);
  Assert(d_node != NULL, "Unexpected NULL expression pointer!");
  PrettyCheckArgument(d_node->hasOperator(), *this,
                      "Expr::getOperator() called on an Expr with no operator");
  return Expr(d_exprManager, new Node(d_node->getOperator()));
}

bool Expr::isParameterized() const
{
  ExprManagerScope ems(*this);
  Assert(d_node != NULL, "Unexpected NULL expression pointer!");
  return d_node->getMetaKind() == kind::metakind::PARAMETERIZED;
}

Type Expr::getType(bool check) const
{
  ExprManagerScope ems(*this);
  Assert(d_node != NULL, "Unexpected NULL expression pointer!");
  PrettyCheckArgument(!d_node->isNull(), this,
                      "Can't get type of null expression!");
  return d_exprManager->getType(*this, check);
}

Expr Expr::substitute(Expr e, Expr replacement) const {
  ExprManagerScope ems(*this);
  return Expr(d_exprManager, new Node(d_node->substitute(TNode(*e.d_node), TNode(*replacement.d_node))));
}

template <class Iterator>
class NodeIteratorAdaptor : public std::iterator<std::input_iterator_tag, Node> {
  Iterator d_iterator;
public:
  NodeIteratorAdaptor(Iterator i) : d_iterator(i) {
  }
  NodeIteratorAdaptor& operator++() { ++d_iterator; return *this; }
  NodeIteratorAdaptor operator++(int) { NodeIteratorAdaptor i(d_iterator); ++d_iterator; return i; }
  bool operator==(NodeIteratorAdaptor i) { return d_iterator == i.d_iterator; }
  bool operator!=(NodeIteratorAdaptor i) { return !(*this == i); }
  Node operator*() { return Node::fromExpr(*d_iterator); }
};/* class NodeIteratorAdaptor */

template <class Iterator>
static inline NodeIteratorAdaptor<Iterator> mkNodeIteratorAdaptor(Iterator i) {
  return NodeIteratorAdaptor<Iterator>(i);
}

Expr Expr::substitute(const std::vector<Expr> exes,
                      const std::vector<Expr>& replacements) const {
  ExprManagerScope ems(*this);
  return Expr(d_exprManager,
              new Node(d_node->substitute(mkNodeIteratorAdaptor(exes.begin()),
                                          mkNodeIteratorAdaptor(exes.end()),
                                          mkNodeIteratorAdaptor(replacements.begin()),
                                          mkNodeIteratorAdaptor(replacements.end()))));
}

template <class Iterator>
class NodePairIteratorAdaptor : public std::iterator<std::input_iterator_tag, pair<Node, Node> > {
  Iterator d_iterator;
public:
  NodePairIteratorAdaptor(Iterator i) : d_iterator(i) {
  }
  NodePairIteratorAdaptor& operator++() { ++d_iterator; return *this; }
  NodePairIteratorAdaptor operator++(int) { NodePairIteratorAdaptor i(d_iterator); ++d_iterator; return i; }
  bool operator==(NodePairIteratorAdaptor i) { return d_iterator == i.d_iterator; }
  bool operator!=(NodePairIteratorAdaptor i) { return !(*this == i); }
  pair<Node, Node> operator*() { return make_pair(Node::fromExpr((*d_iterator).first), Node::fromExpr((*d_iterator).second)); }
};/* class NodePairIteratorAdaptor */

template <class Iterator>
static inline NodePairIteratorAdaptor<Iterator> mkNodePairIteratorAdaptor(Iterator i) {
  return NodePairIteratorAdaptor<Iterator>(i);
}

Expr Expr::substitute(const std::unordered_map<Expr, Expr, ExprHashFunction> map) const {
  ExprManagerScope ems(*this);
  return Expr(d_exprManager, new Node(d_node->substitute(mkNodePairIteratorAdaptor(map.begin()), mkNodePairIteratorAdaptor(map.end()))));
}

Expr::const_iterator::const_iterator()
    : d_exprManager(nullptr), d_iterator(nullptr) {}

Expr::const_iterator::const_iterator(ExprManager* em, void* v)
    : d_exprManager(em), d_iterator(v) {}

Expr::const_iterator::const_iterator(const const_iterator& it)
    : d_exprManager(nullptr), d_iterator(nullptr) {
  if (it.d_iterator != nullptr) {
    d_exprManager = it.d_exprManager;
    ExprManagerScope ems(*d_exprManager);
    d_iterator =
        new Node::iterator(*reinterpret_cast<Node::iterator*>(it.d_iterator));
  }
}

Expr::const_iterator& Expr::const_iterator::operator=(const const_iterator& it) {
  if(d_iterator != NULL) {
    ExprManagerScope ems(*d_exprManager);
    delete reinterpret_cast<Node::iterator*>(d_iterator);
  }
  d_exprManager = it.d_exprManager;
  ExprManagerScope ems(*d_exprManager);
  d_iterator = new Node::iterator(*reinterpret_cast<Node::iterator*>(it.d_iterator));
  return *this;
}
Expr::const_iterator::~const_iterator() {
  if(d_iterator != NULL) {
    ExprManagerScope ems(*d_exprManager);
    delete reinterpret_cast<Node::iterator*>(d_iterator);
  }
}
bool Expr::const_iterator::operator==(const const_iterator& it) const {
  if(d_iterator == NULL || it.d_iterator == NULL) {
    return false;
  }
  return *reinterpret_cast<Node::iterator*>(d_iterator) ==
    *reinterpret_cast<Node::iterator*>(it.d_iterator);
}
Expr::const_iterator& Expr::const_iterator::operator++() {
  Assert(d_iterator != NULL);
  ExprManagerScope ems(*d_exprManager);
  ++*reinterpret_cast<Node::iterator*>(d_iterator);
  return *this;
}
Expr::const_iterator Expr::const_iterator::operator++(int) {
  Assert(d_iterator != NULL);
  ExprManagerScope ems(*d_exprManager);
  const_iterator it = *this;
  ++*reinterpret_cast<Node::iterator*>(d_iterator);
  return it;
}
Expr Expr::const_iterator::operator*() const {
  Assert(d_iterator != NULL);
  ExprManagerScope ems(*d_exprManager);
  return (**reinterpret_cast<Node::iterator*>(d_iterator)).toExpr();
}

Expr::const_iterator Expr::begin() const {
  ExprManagerScope ems(*d_exprManager);
  return Expr::const_iterator(d_exprManager, new Node::iterator(d_node->begin()));
}

Expr::const_iterator Expr::end() const {
  ExprManagerScope ems(*d_exprManager);
  return Expr::const_iterator(d_exprManager, new Node::iterator(d_node->end()));
}

std::string Expr::toString() const {
  ExprManagerScope ems(*this);
  Assert(d_node != NULL, "Unexpected NULL expression pointer!");
  return d_node->toString();
}

bool Expr::isNull() const {
  ExprManagerScope ems(*this);
  Assert(d_node != NULL, "Unexpected NULL expression pointer!");
  return d_node->isNull();
}

bool Expr::isVariable() const {
  ExprManagerScope ems(*this);
  Assert(d_node != NULL, "Unexpected NULL expression pointer!");
  return d_node->getMetaKind() == kind::metakind::VARIABLE;
}

bool Expr::isConst() const {
  ExprManagerScope ems(*this);
  Assert(d_node != NULL, "Unexpected NULL expression pointer!");
  return d_node->isConst();
}

bool Expr::hasFreeVariable() const
{
  ExprManagerScope ems(*this);
  Assert(d_node != NULL, "Unexpected NULL expression pointer!");
  return expr::hasFreeVar(*d_node);
}

void Expr::toStream(std::ostream& out, int depth, bool types, size_t dag,
                    OutputLanguage language) const {
  ExprManagerScope ems(*this);
  d_node->toStream(out, depth, types, dag, language);
}

Node Expr::getNode() const { return *d_node; }
TNode Expr::getTNode() const { return *d_node; }
Expr Expr::notExpr() const {
  Assert(d_exprManager != NULL,
         "Don't have an expression manager for this expression!");
  return d_exprManager->mkExpr(NOT, *this);
}

Expr Expr::andExpr(const Expr& e) const {
  Assert(d_exprManager != NULL,
         "Don't have an expression manager for this expression!");
  PrettyCheckArgument(d_exprManager == e.d_exprManager, e,
                      "Different expression managers!");
  return d_exprManager->mkExpr(AND, *this, e);
}

Expr Expr::orExpr(const Expr& e) const {
  Assert(d_exprManager != NULL,
         "Don't have an expression manager for this expression!");
  PrettyCheckArgument(d_exprManager == e.d_exprManager, e,
                      "Different expression managers!");
  return d_exprManager->mkExpr(OR, *this, e);
}

Expr Expr::xorExpr(const Expr& e) const {
  Assert(d_exprManager != NULL,
         "Don't have an expression manager for this expression!");
  PrettyCheckArgument(d_exprManager == e.d_exprManager, e,
                      "Different expression managers!");
  return d_exprManager->mkExpr(XOR, *this, e);
}

Expr Expr::eqExpr(const Expr& e) const
{
  Assert(d_exprManager != NULL,
         "Don't have an expression manager for this expression!");
  PrettyCheckArgument(d_exprManager == e.d_exprManager, e,
                      "Different expression managers!");
  return d_exprManager->mkExpr(EQUAL, *this, e);
}

Expr Expr::impExpr(const Expr& e) const {
  Assert(d_exprManager != NULL,
         "Don't have an expression manager for this expression!");
  PrettyCheckArgument(d_exprManager == e.d_exprManager, e,
                      "Different expression managers!");
  return d_exprManager->mkExpr(IMPLIES, *this, e);
}

Expr Expr::iteExpr(const Expr& then_e,
                           const Expr& else_e) const {
  Assert(d_exprManager != NULL,
         "Don't have an expression manager for this expression!");
  PrettyCheckArgument(d_exprManager == then_e.d_exprManager, then_e,
                      "Different expression managers!");
  PrettyCheckArgument(d_exprManager == else_e.d_exprManager, else_e,
                      "Different expression managers!");
  return d_exprManager->mkExpr(ITE, *this, then_e, else_e);
}

void Expr::printAst(std::ostream & o, int indent) const {
  ExprManagerScope ems(*this);
  getNode().printAst(o, indent);
}

void Expr::debugPrint() {
#ifndef CVC4_MUZZLE
  printAst(Warning());
  Warning().flush();
#endif /* ! CVC4_MUZZLE */
}

${getConst_implementations}

namespace expr {

static Node exportConstant(TNode n, NodeManager* to, ExprManagerMapCollection& vmap) {
  Assert(n.isConst());
  Debug("export") << "constant: " << n << std::endl;

  if(n.getKind() == kind::STORE_ALL) {
    // Special export for ArrayStoreAll.
    //
    // Ultimately we'll need special cases also for RecordUpdate,
    // TupleUpdate, AscriptionType, and other constant-metakinded
    // expressions that embed types.  For now datatypes aren't supported
    // for export so those don't matter.
    ExprManager* toEm = to->toExprManager();
    const ArrayStoreAll& asa = n.getConst<ArrayStoreAll>();
    return to->mkConst(ArrayStoreAll(asa.getType().exportTo(toEm, vmap),
                                     asa.getExpr().exportTo(toEm, vmap)));
  }

  switch(n.getKind()) {
${exportConstant_cases}

  default: Unhandled(n.getKind());
  }

}/* exportConstant() */

}/* CVC4::expr namespace */
}/* CVC4 namespace */
