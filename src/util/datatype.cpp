/*********************                                                        */
/*! \file datatype.cpp
 ** \verbatim
 ** Original author: mdeters
 ** Major contributors: none
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010, 2011  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief A class representing a Datatype definition
 **
 ** A class representing a Datatype definition for the theory of
 ** inductive datatypes.
 **/

#include <string>
#include <sstream>

#include "util/datatype.h"
#include "expr/type.h"
#include "expr/expr_manager.h"
#include "expr/node.h"

using namespace std;

namespace CVC4 {

namespace expr {
  namespace attr {
    struct DatatypeIndexTag {};
  }
}

typedef expr::Attribute<expr::attr::DatatypeIndexTag, uint64_t> DatatypeIndexAttr;

const Datatype& Datatype::datatypeOf(Expr item) {
  TypeNode t = Node::fromExpr(item).getType();
  switch(t.getKind()) {
  case kind::CONSTRUCTOR_TYPE:
    return t[t.getNumChildren() - 1].getConst<Datatype>();
  case kind::SELECTOR_TYPE:
  case kind::TESTER_TYPE:
    return t[0].getConst<Datatype>();
  default:
    Unhandled("arg must be a datatype constructor, selector, or tester");
  }
}

size_t Datatype::indexOf(Expr item) {
  AssertArgument(item.getType().isConstructor() ||
                 item.getType().isTester() ||
                 item.getType().isSelector(),
                 item,
                 "arg must be a datatype constructor, selector, or tester");
  TNode n = Node::fromExpr(item);
  Assert(n.hasAttribute(DatatypeIndexAttr()));
  return n.getAttribute(DatatypeIndexAttr());
}

void Datatype::resolve(ExprManager* em,
                       const std::map<std::string, DatatypeType>& resolutions)
  throw(AssertionException, DatatypeResolutionException) {

  CheckArgument(em != NULL, "cannot resolve a Datatype with a NULL expression manager");
  CheckArgument(!d_resolved, "cannot resolve a Datatype twice");
  CheckArgument(resolutions.find(d_name) != resolutions.end(), "Datatype::resolve(): resolutions doesn't contain me!");
  DatatypeType self = (*resolutions.find(d_name)).second;
  CheckArgument(&self.getDatatype() == this, "Datatype::resolve(): resolutions doesn't contain me!");
  d_resolved = true;
  size_t index = 0;
  for(iterator i = begin(), i_end = end(); i != i_end; ++i) {
    (*i).resolve(em, self, resolutions);
    Assert((*i).isResolved());
    Node::fromExpr((*i).d_constructor).setAttribute(DatatypeIndexAttr(), index);
    Node::fromExpr((*i).d_tester).setAttribute(DatatypeIndexAttr(), index++);
  }
  Assert(index == getNumConstructors());
}

void Datatype::addConstructor(const Constructor& c) {
  CheckArgument(!d_resolved, this,
                "cannot add a constructor to a finalized Datatype");
  d_constructors.push_back(c);
}

bool Datatype::operator==(const Datatype& other) const throw() {
  // two datatypes are == iff the name is the same and they have
  // exactly matching constructors (in the same order)

  if(this == &other) {
    return true;
  }

  if(isResolved() != other.isResolved()) {
    return false;
  }

  if(d_name != other.d_name ||
     getNumConstructors() != other.getNumConstructors()) {
    return false;
  }
  for(const_iterator i = begin(), j = other.begin(); i != end(); ++i, ++j) {
    Assert(j != other.end());
    // two constructors are == iff they have the same name, their
    // constructors and testers are equal and they have exactly
    // matching args (in the same order)
    if((*i).getName() != (*j).getName() ||
       (*i).getNumArgs() != (*j).getNumArgs()) {
      return false;
    }
    // testing equivalence of constructors and testers is harder b/c
    // this constructor might not be resolved yet; only compare them
    // if they are both resolved
    Assert(isResolved() == !(*i).d_constructor.isNull() &&
           isResolved() == !(*i).d_tester.isNull() &&
           (*i).d_constructor.isNull() == (*j).d_constructor.isNull() &&
           (*i).d_tester.isNull() == (*j).d_tester.isNull());
    if(!(*i).d_constructor.isNull() && (*i).d_constructor != (*j).d_constructor) {
      return false;
    }
    if(!(*i).d_tester.isNull() && (*i).d_tester != (*j).d_tester) {
      return false;
    }
    for(Constructor::const_iterator k = (*i).begin(), l = (*j).begin(); k != (*i).end(); ++k, ++l) {
      Assert(l != (*j).end());
      if((*k).getName() != (*l).getName()) {
        return false;
      }
      // testing equivalence of selectors is harder b/c args might not
      // be resolved yet
      Assert(isResolved() == (*k).isResolved() &&
             (*k).isResolved() == (*l).isResolved());
      if((*k).isResolved()) {
        // both are resolved, so simply compare the selectors directly
        if((*k).d_selector != (*l).d_selector) {
          return false;
        }
      } else {
        // neither is resolved, so compare their (possibly unresolved)
        // types; we don't know if they'll be resolved the same way,
        // so we can't ever say unresolved types are equal
        if(!(*k).d_selector.isNull() && !(*l).d_selector.isNull()) {
          if((*k).d_selector.getType() != (*l).d_selector.getType()) {
            return false;
          }
        } else {
          if((*k).isUnresolvedSelf() && (*l).isUnresolvedSelf()) {
            // Fine, the selectors are equal if the rest of the
            // enclosing datatypes are equal...
          } else {
            return false;
          }
        }
      }
    }
  }
  return true;
}

const Datatype::Constructor& Datatype::operator[](size_t index) const {
  CheckArgument(index < getNumConstructors(), index, "index out of bounds");
  return d_constructors[index];
}

void Datatype::Constructor::resolve(ExprManager* em, DatatypeType self,
                                    const std::map<std::string, DatatypeType>& resolutions)
  throw(AssertionException, DatatypeResolutionException) {
  CheckArgument(em != NULL, "cannot resolve a Datatype with a NULL expression manager");
  CheckArgument(!isResolved(),
                "cannot resolve a Datatype constructor twice; "
                "perhaps the same constructor was added twice, "
                "or to two datatypes?");
  size_t index = 0;
  for(iterator i = begin(), i_end = end(); i != i_end; ++i) {
    if((*i).d_selector.isNull()) {
      string typeName = (*i).d_name.substr((*i).d_name.find('\0') + 1);
      (*i).d_name.resize((*i).d_name.find('\0'));
      if(typeName == "") {
        (*i).d_selector = em->mkVar((*i).d_name, em->mkSelectorType(self, self));
      } else {
        map<string, DatatypeType>::const_iterator j = resolutions.find(typeName);
        if(j == resolutions.end()) {
          stringstream msg;
          msg << "cannot resolve type \"" << typeName << "\" "
              << "in selector \"" << (*i).d_name << "\" "
              << "of constructor \"" << d_name << "\"";
          throw DatatypeResolutionException(msg.str());
        } else {
          (*i).d_selector = em->mkVar((*i).d_name, em->mkSelectorType(self, (*j).second));
        }
      }
    } else {
      (*i).d_selector = em->mkVar((*i).d_name, em->mkSelectorType(self, (*i).d_selector.getType()));
    }
    Node::fromExpr((*i).d_selector).setAttribute(DatatypeIndexAttr(), index++);
    (*i).d_resolved = true;
  }

  Assert(index == getNumArgs());

  // Set constructor/tester last, since Constructor::isResolved()
  // returns true when d_tester is not the null Expr.  If something
  // fails above, we want Constuctor::isResolved() to remain "false"
  d_tester = em->mkVar(d_name.substr(d_name.find('\0') + 1), em->mkTesterType(self));
  d_name.resize(d_name.find('\0'));
  d_constructor = em->mkVar(d_name, em->mkConstructorType(*this, self));
}

Datatype::Constructor::Constructor(std::string name, std::string tester) :
  // We don't want to introduce a new data member, because eventually
  // we're going to be a constant stuffed inside a node.  So we stow
  // the tester name away inside the constructor name until
  // resolution.
  d_name(name + '\0' + tester),
  d_tester(),
  d_args() {
  CheckArgument(name != "", name, "cannot construct a datatype constructor without a name");
  CheckArgument(!tester.empty(), tester, "cannot construct a datatype constructor without a tester");
}

void Datatype::Constructor::addArg(std::string selectorName, Type selectorType) {
  // We don't want to introduce a new data member, because eventually
  // we're going to be a constant stuffed inside a node.  So we stow
  // the selector type away inside a var until resolution (when we can
  // create the proper selector type)
  CheckArgument(!isResolved(), this, "cannot modify a finalized Datatype constructor");
  CheckArgument(!selectorType.isNull(), selectorType, "cannot add a null selector type");
  Expr type = selectorType.getExprManager()->mkVar(selectorType);
  Debug("datatypes") << type << endl;
  d_args.push_back(Arg(selectorName, type));
}

void Datatype::Constructor::addArg(std::string selectorName, Datatype::UnresolvedType selectorType) {
  // We don't want to introduce a new data member, because eventually
  // we're going to be a constant stuffed inside a node.  So we stow
  // the selector type away after a NUL in the name string until
  // resolution (when we can create the proper selector type)
  CheckArgument(!isResolved(), this, "cannot modify a finalized Datatype constructor");
  CheckArgument(selectorType.getName() != "", selectorType, "cannot add a null selector type");
  d_args.push_back(Arg(selectorName + '\0' + selectorType.getName(), Expr()));
}

void Datatype::Constructor::addArg(std::string selectorName, Datatype::SelfType) {
  // We don't want to introduce a new data member, because eventually
  // we're going to be a constant stuffed inside a node.  So we mark
  // the name string with a NUL to indicate that we have a
  // self-selecting selector until resolution (when we can create the
  // proper selector type)
  CheckArgument(!isResolved(), this, "cannot modify a finalized Datatype constructor");
  d_args.push_back(Arg(selectorName + '\0', Expr()));
}

std::string Datatype::Constructor::getName() const throw() {
  string name = d_name;
  if(!isResolved()) {
    name.resize(name.find('\0'));
  }
  return name;
}

Expr Datatype::Constructor::getConstructor() const {
  CheckArgument(isResolved(), this, "this datatype constructor not yet resolved");
  return d_constructor;
}

Expr Datatype::Constructor::getTester() const {
  CheckArgument(isResolved(), this, "this datatype constructor not yet resolved");
  return d_tester;
}

const Datatype::Constructor::Arg& Datatype::Constructor::operator[](size_t index) const {
  CheckArgument(index < getNumArgs(), index, "index out of bounds");
  return d_args[index];
}

Datatype::Constructor::Arg::Arg(std::string name, Expr selector) :
  d_name(name),
  d_selector(selector),
  d_resolved(false) {
  CheckArgument(name != "", name, "cannot construct a datatype constructor arg without a name");
}

std::string Datatype::Constructor::Arg::getName() const throw() {
  string name = d_name;
  const size_t nul = name.find('\0');
  if(nul != string::npos) {
    name.resize(nul);
  }
  return name;
}

Expr Datatype::Constructor::Arg::getSelector() const {
  CheckArgument(isResolved(), this, "cannot get a selector for an unresolved datatype constructor");
  return d_selector;
}

bool Datatype::Constructor::Arg::isUnresolvedSelf() const throw() {
  return d_selector.isNull() && d_name.size() == d_name.find('\0') + 1;
}

std::string Datatype::Constructor::Arg::getSelectorTypeName() const {
  Type t;
  if(isResolved()) {
    t = SelectorType(d_selector.getType()).getRangeType();
  } else {
    if(d_selector.isNull()) {
      string typeName = d_name.substr(d_name.find('\0') + 1);
      return (typeName == "") ? "[self]" : typeName;
    } else {
      t = d_selector.getType();
    }
  }

  return t.isDatatype() ? DatatypeType(t).getDatatype().getName() : t.toString();
}

std::ostream& operator<<(std::ostream& os, const Datatype& dt) {
  // can only output datatypes in the CVC4 native language
  Expr::setlanguage::Scope ls(os, language::output::LANG_CVC4);

  os << "DATATYPE " << dt.getName() << " =" << endl;
  Datatype::const_iterator i = dt.begin(), i_end = dt.end();
  if(i != i_end) {
    os << "  ";
    do {
      os << *i << endl;
      if(++i != i_end) {
        os << "| ";
      }
    } while(i != i_end);
  }
  os << "END;" << endl;

  return os;
}

std::ostream& operator<<(std::ostream& os, const Datatype::Constructor& ctor) {
  // can only output datatypes in the CVC4 native language
  Expr::setlanguage::Scope ls(os, language::output::LANG_CVC4);

  os << ctor.getName();

  Datatype::Constructor::const_iterator i = ctor.begin(), i_end = ctor.end();
  if(i != i_end) {
    os << "(";
    do {
      os << *i;
      if(++i != i_end) {
        os << ", ";
      }
    } while(i != i_end);
    os << ")";
  }

  return os;
}

std::ostream& operator<<(std::ostream& os, const Datatype::Constructor::Arg& arg) {
  // can only output datatypes in the CVC4 native language
  Expr::setlanguage::Scope ls(os, language::output::LANG_CVC4);

  os << arg.getName() << ": " << arg.getSelectorTypeName();

  return os;
}

}/* CVC4 namespace */
