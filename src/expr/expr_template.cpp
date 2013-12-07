/*********************                                                        */
/*! \file expr_template.cpp
 ** \verbatim
 ** Original author: Morgan Deters
 ** Major contributors: Dejan Jovanovic
 ** Minor contributors (to current version): Tim King, Christopher L. Conway, Kshitij Bansal
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2013  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief Public-facing expression interface, implementation.
 **
 ** Public-facing expression interface, implementation.
 **/

#include "expr/expr.h"
#include "expr/node.h"
#include "expr/expr_manager_scope.h"
#include "expr/variable_type_map.h"
#include "util/cvc4_assert.h"
#include "expr/node_manager_attributes.h"

#include <vector>
#include <iterator>
#include <utility>

${includes}

// This is a hack, but an important one: if there's an error, the
// compiler directs the user to the template file instead of the
// generated one.  We don't want the user to modify the generated one,
// since it'll get overwritten on a later build.
#line 35 "${template}"

using namespace CVC4::kind;
using namespace std;

namespace CVC4 {

class ExprManager;

namespace expr {

const int ExprSetDepth::s_iosIndex = std::ios_base::xalloc();
const int ExprPrintTypes::s_iosIndex = std::ios_base::xalloc();
const int ExprDag::s_iosIndex = std::ios_base::xalloc();
const int ExprSetLanguage::s_iosIndex = std::ios_base::xalloc();

}/* CVC4::expr namespace */

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

TypeCheckingException::TypeCheckingException(const TypeCheckingException& t) throw() :
  Exception(t.d_msg), d_expr(new Expr(t.getExpression())) {
}

TypeCheckingException::TypeCheckingException(const Expr& expr, std::string message) throw() :
  Exception(message), d_expr(new Expr(expr)) {
}

TypeCheckingException::TypeCheckingException(ExprManager* em,
                                             const TypeCheckingExceptionPrivate* exc) throw() :
  Exception(exc->getMessage()), d_expr(new Expr(em, new Node(exc->getNode()))) {
}

TypeCheckingException::~TypeCheckingException() throw() {
  delete d_expr;
}

void TypeCheckingException::toStream(std::ostream& os) const throw() {
  os << "Error during type checking: " << d_msg << endl
     << "The ill-typed expression: " << *d_expr;
}

Expr TypeCheckingException::getExpression() const throw() {
  return *d_expr;
}

Expr::Expr() :
  d_node(new Node),
  d_exprManager(NULL) {
}

Expr::Expr(ExprManager* em, Node* node) :
  d_node(node),
  d_exprManager(em) {
}

Expr::Expr(const Expr& e) :
  d_node(new Node(*e.d_node)),
  d_exprManager(e.d_exprManager) {
}

Expr::~Expr() {
  ExprManagerScope ems(*this);
  delete d_node;
}

ExprManager* Expr::getExprManager() const {
  return d_exprManager;
}

namespace expr {

static Node exportConstant(TNode n, NodeManager* to);

class ExportPrivate {
private:
  typedef std::hash_map <NodeTemplate<false>, NodeTemplate<true>, TNodeHashFunction> ExportCache;
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
      return exportConstant(n, NodeManager::fromExprManager(to));
    } else if(n.isVar()) {
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
          // temporarily set the node manager to NULL; this gets around
          // a check that mkVar isn't called internally

          if(n.getKind() == kind::BOUND_VAR_LIST || n.getKind() == kind::BOUND_VARIABLE) {
            NodeManagerScope nullScope(NULL);
            to_e = to->mkBoundVar(name, type);// FIXME thread safety
          } else if(n.getKind() == kind::VARIABLE) {
            bool isGlobal;
            Node::fromExpr(from_e).getAttribute(GlobalVarAttr(), isGlobal);
            NodeManagerScope nullScope(NULL);
            to_e = to->mkVar(name, type, isGlobal ? ExprManager::VAR_FLAG_GLOBAL : flags);// FIXME thread safety
          } else if(n.getKind() == kind::SKOLEM) {
            // skolems are only available at the Node level (not the Expr level)
            TypeNode typeNode = TypeNode::fromType(type);
            NodeManager* to_nm = NodeManager::fromExprManager(to);
            Node n = to_nm->mkSkolem(name, typeNode, "is a skolem variable imported from another ExprManager");// FIXME thread safety
            to_e = n.toExpr();
          } else {
            Unhandled();
          }

          Debug("export") << "+ exported var `" << from_e << "'[" << from_e.getId() << "] with name `" << name << "' and type `" << from_e.getType() << "' to `" << to_e << "'[" << to_e.getId() << "] with type `" << type << "'" << std::endl;
        } else {
          // temporarily set the node manager to NULL; this gets around
          // a check that mkVar isn't called internally
          NodeManagerScope nullScope(NULL);
          to_e = to->mkVar(type);// FIXME thread safety
          Debug("export") << "+ exported unnamed var `" << from_e << "' with type `" << from_e.getType() << "' to `" << to_e << "' with type `" << type << "'" << std::endl;
        }
        uint64_t to_int = (uint64_t)(to_e.getNode().d_nv);
        uint64_t from_int = (uint64_t)(from_e.getNode().d_nv);
        vmap.d_from[to_int] = from_int;
        vmap.d_to[from_int] = to_int;
        vmap.d_typeMap[to_e] = from_e;// insert other direction too
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
        ExprManagerScope ems(*to);
        Debug("export") << "children for export from " << n << std::endl;
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

unsigned long Expr::getId() const {
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
  CheckArgument(d_node->hasOperator(), *this,
                "Expr::getOperator() called on an Expr with no operator");
  return Expr(d_exprManager, new Node(d_node->getOperator()));
}

Type Expr::getType(bool check) const throw (TypeCheckingException) {
  ExprManagerScope ems(*this);
  Assert(d_node != NULL, "Unexpected NULL expression pointer!");
  CheckArgument(!d_node->isNull(), this, "Can't get type of null expression!");
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

Expr Expr::substitute(const std::hash_map<Expr, Expr, ExprHashFunction> map) const {
  ExprManagerScope ems(*this);
  return Expr(d_exprManager, new Node(d_node->substitute(mkNodePairIteratorAdaptor(map.begin()), mkNodePairIteratorAdaptor(map.end()))));
}

Expr::const_iterator::const_iterator() :
  d_iterator(NULL) {
}
Expr::const_iterator::const_iterator(ExprManager* em, void* v) :
  d_exprManager(em),
  d_iterator(v) {
}
Expr::const_iterator::const_iterator(const const_iterator& it) {
  if(it.d_iterator == NULL) {
    d_iterator = NULL;
  } else {
    d_exprManager = it.d_exprManager;
    ExprManagerScope ems(*d_exprManager);
    d_iterator = new Node::iterator(*reinterpret_cast<Node::iterator*>(it.d_iterator));
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

void Expr::toStream(std::ostream& out, int depth, bool types, size_t dag,
                    OutputLanguage language) const {
  ExprManagerScope ems(*this);
  d_node->toStream(out, depth, types, dag, language);
}

Node Expr::getNode() const throw() {
  return *d_node;
}

TNode Expr::getTNode() const throw() {
  return *d_node;
}

Expr Expr::notExpr() const {
  Assert(d_exprManager != NULL,
         "Don't have an expression manager for this expression!");
  return d_exprManager->mkExpr(NOT, *this);
}

Expr Expr::andExpr(const Expr& e) const {
  Assert(d_exprManager != NULL,
         "Don't have an expression manager for this expression!");
  CheckArgument(d_exprManager == e.d_exprManager, e,
                "Different expression managers!");
  return d_exprManager->mkExpr(AND, *this, e);
}

Expr Expr::orExpr(const Expr& e) const {
  Assert(d_exprManager != NULL,
         "Don't have an expression manager for this expression!");
  CheckArgument(d_exprManager == e.d_exprManager, e,
                "Different expression managers!");
  return d_exprManager->mkExpr(OR, *this, e);
}

Expr Expr::xorExpr(const Expr& e) const {
  Assert(d_exprManager != NULL,
         "Don't have an expression manager for this expression!");
  CheckArgument(d_exprManager == e.d_exprManager, e,
                "Different expression managers!");
  return d_exprManager->mkExpr(XOR, *this, e);
}

Expr Expr::iffExpr(const Expr& e) const {
  Assert(d_exprManager != NULL,
         "Don't have an expression manager for this expression!");
  CheckArgument(d_exprManager == e.d_exprManager, e,
                "Different expression managers!");
  return d_exprManager->mkExpr(IFF, *this, e);
}

Expr Expr::impExpr(const Expr& e) const {
  Assert(d_exprManager != NULL,
         "Don't have an expression manager for this expression!");
  CheckArgument(d_exprManager == e.d_exprManager, e,
                "Different expression managers!");
  return d_exprManager->mkExpr(IMPLIES, *this, e);
}

Expr Expr::iteExpr(const Expr& then_e,
                           const Expr& else_e) const {
  Assert(d_exprManager != NULL,
         "Don't have an expression manager for this expression!");
  CheckArgument(d_exprManager == then_e.d_exprManager, then_e,
                "Different expression managers!");
  CheckArgument(d_exprManager == else_e.d_exprManager, else_e,
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

static Node exportConstant(TNode n, NodeManager* to) {
  Assert(n.isConst());
  switch(n.getKind()) {
${exportConstant_cases}

  default: Unhandled(n.getKind());
  }
}/* exportConstant() */

}/* CVC4::expr namespace */
}/* CVC4 namespace */
