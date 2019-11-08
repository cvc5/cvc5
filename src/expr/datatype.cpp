/*********************                                                        */
/*! \file datatype.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Morgan Deters, Tim King
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief A class representing a Datatype definition
 **
 ** A class representing a Datatype definition for the theory of
 ** inductive datatypes.
 **/
#include "expr/datatype.h"

#include <string>
#include <sstream>

#include "base/check.h"
#include "expr/attribute.h"
#include "expr/expr_manager.h"
#include "expr/expr_manager_scope.h"
#include "expr/node.h"
#include "expr/node_algorithm.h"
#include "expr/node_manager.h"
#include "expr/type.h"
#include "expr/type_matcher.h"
#include "options/datatypes_options.h"
#include "options/set_language.h"
#include "theory/type_enumerator.h"
#include "theory/datatypes/dtype.h"

using namespace std;

namespace CVC4 {

namespace expr {
  namespace attr {
    struct DatatypeIndexTag {};
    struct DatatypeConsIndexTag {};
    struct DatatypeFiniteTag {};
    struct DatatypeFiniteComputedTag {};
    struct DatatypeUFiniteTag {};
    struct DatatypeUFiniteComputedTag {};
  }/* CVC4::expr::attr namespace */
}/* CVC4::expr namespace */

typedef expr::Attribute<expr::attr::DatatypeIndexTag, uint64_t> DatatypeIndexAttr;
typedef expr::Attribute<expr::attr::DatatypeConsIndexTag, uint64_t> DatatypeConsIndexAttr;
typedef expr::Attribute<expr::attr::DatatypeFiniteTag, bool> DatatypeFiniteAttr;
typedef expr::Attribute<expr::attr::DatatypeFiniteComputedTag, bool> DatatypeFiniteComputedAttr;
typedef expr::Attribute<expr::attr::DatatypeUFiniteTag, bool> DatatypeUFiniteAttr;
typedef expr::Attribute<expr::attr::DatatypeUFiniteComputedTag, bool> DatatypeUFiniteComputedAttr;

Datatype::~Datatype(){
  delete d_record;
}

Datatype::Datatype(std::string name, bool isCo)
    : d_internal(new DType(name, isCo)),
      d_record(NULL),
      d_constructors() {}

Datatype::Datatype(std::string name, const std::vector<Type>& params,
                          bool isCo)
    : d_internal(new DType(name, isCo)),
      d_record(NULL),
      d_constructors(){}

const Datatype& Datatype::datatypeOf(Expr item) {
  ExprManagerScope ems(item);
  TypeNode t = Node::fromExpr(item).getType();
  switch(t.getKind()) {
  case kind::CONSTRUCTOR_TYPE:
    return DatatypeType(t[t.getNumChildren() - 1].toType()).getDatatype();
  case kind::SELECTOR_TYPE:
  case kind::TESTER_TYPE:
    return DatatypeType(t[0].toType()).getDatatype();
  default:
    Unhandled() << "arg must be a datatype constructor, selector, or tester";
  }
}

size_t Datatype::indexOf(Expr item) {
  ExprManagerScope ems(item);
  PrettyCheckArgument(item.getType().isConstructor() ||
                item.getType().isTester() ||
                item.getType().isSelector(),
                item,
                "arg must be a datatype constructor, selector, or tester");
  return indexOfInternal(item);
}

size_t Datatype::indexOfInternal(Expr item)
{
  TNode n = Node::fromExpr(item);
  if( item.getKind()==kind::APPLY_TYPE_ASCRIPTION ){
    return indexOf( item[0] );
  }else{
    Assert(n.hasAttribute(DatatypeIndexAttr()));
    return n.getAttribute(DatatypeIndexAttr());
  }
}

size_t Datatype::cindexOf(Expr item) {
  ExprManagerScope ems(item);
  PrettyCheckArgument(item.getType().isSelector(),
                item,
                "arg must be a datatype selector");
  return cindexOfInternal(item);
}
size_t Datatype::cindexOfInternal(Expr item)
{
  TNode n = Node::fromExpr(item);
  if( item.getKind()==kind::APPLY_TYPE_ASCRIPTION ){
    return cindexOf( item[0] );
  }else{
    Assert(n.hasAttribute(DatatypeConsIndexAttr()));
    return n.getAttribute(DatatypeConsIndexAttr());
  }
}

void Datatype::resolve(ExprManager* em,
                       const std::map<std::string, DatatypeType>& resolutions,
                       const std::vector<Type>& placeholders,
                       const std::vector<Type>& replacements,
                       const std::vector< SortConstructorType >& paramTypes,
                       const std::vector< DatatypeType >& paramReplacements)
{
  PrettyCheckArgument(em != NULL, em, "cannot resolve a Datatype with a NULL expression manager");
  PrettyCheckArgument(!isResolved(), this, "cannot resolve a Datatype twice");
  PrettyCheckArgument(resolutions.find(getName()) != resolutions.end(), resolutions,
                "Datatype::resolve(): resolutions doesn't contain me!");
  PrettyCheckArgument(placeholders.size() == replacements.size(), placeholders,
                "placeholders and replacements must be the same size");
  PrettyCheckArgument(paramTypes.size() == paramReplacements.size(), paramTypes,
                "paramTypes and paramReplacements must be the same size");
  PrettyCheckArgument(getNumConstructors() > 0, *this, "cannot resolve a Datatype that has no constructors");
  
  // we're using some internals, so we have to set up this library context
  ExprManagerScope ems(*em);
  
  Trace("dt-debug") << "Datatype::resolve: " << getName() << std::endl;
  
  std::map<std::string, TypeNode> resolutionsn;
  std::vector<TypeNode> placeholdersn;
  std::vector<TypeNode> replacementsn;
  std::vector< TypeNode > paramTypesn;
  std::vector< TypeNode > paramReplacementsn;
  for (const std::pair<const std::string, DatatypeType>& r : resolutions)
  {
    resolutionsn[r.first] = TypeNode::fromType(r.second);
  }
  for (const Type& t : placeholders)
  {
    placeholdersn.push_back(TypeNode::fromType(t));
  }
  for (const Type& t : replacements)
  {
    replacementsn.push_back(TypeNode::fromType(t));
  }
  for (const Type& t : paramTypes)
  {
    paramTypesn.push_back(TypeNode::fromType(t));
  }
  for (const Type& t : paramReplacements)
  {
    paramReplacementsn.push_back(TypeNode::fromType(t));
  }
  d_internal->resolve(resolutionsn, placeholdersn, replacementsn, paramTypesn, paramReplacementsn);
  Trace("dt-debug") << "Datatype::resolve: finished " << getName() << std::endl;
}

void Datatype::addConstructor(const DatatypeConstructor& c) {
  Trace("dt-debug") << "Datatype::addConstructor" << std::endl;
  PrettyCheckArgument(!isResolved(), this,
                "cannot add a constructor to a finalized Datatype");
  d_constructors.push_back(c);
  d_internal->addConstructor(*c.d_internal);
  Trace("dt-debug") << "Datatype::addConstructor: finished" << std::endl;
}


void Datatype::setSygus( Type st, Expr bvl, bool allow_const, bool allow_all ){
  PrettyCheckArgument(!isResolved(), this,
                      "cannot set sygus type to a finalized Datatype");    
  TypeNode stn = TypeNode::fromType(st);
  Node bvln = Node::fromExpr(bvl);
  d_internal->setSygus(stn, bvln, allow_const, allow_all);
}

void Datatype::addSygusConstructor(Expr op,
                                   const std::string& cname,
                                   const std::vector<Type>& cargs,
                                   std::shared_ptr<SygusPrintCallback> spc,
                                   int weight)
{
  // avoid name clashes
  std::stringstream ss;
  ss << getName() << "_" << getNumConstructors() << "_" << cname;
  std::string name = ss.str();
  std::string testerId("is-");
  testerId.append(name);
  unsigned cweight = weight >= 0 ? weight : (cargs.empty() ? 0 : 1);
  DatatypeConstructor c(name, testerId, cweight);
  c.setSygus(op, spc);
  for( unsigned j=0; j<cargs.size(); j++ ){
    Debug("parser-sygus-debug") << "  arg " << j << " : " << cargs[j] << std::endl;
    std::stringstream sname;
    sname << name << "_" << j;
    c.addArg(sname.str(), cargs[j]);
  }
  addConstructor(c);
}
                                    
void Datatype::setTuple() {
  PrettyCheckArgument(!isResolved(), this, "cannot set tuple to a finalized Datatype");
  d_internal->setTuple();
}

void Datatype::setRecord() {
  PrettyCheckArgument(!isResolved(), this, "cannot set record to a finalized Datatype");
  d_isRecord = true;
}

Cardinality Datatype::getCardinality(Type t) const
{
  PrettyCheckArgument(isResolved(), this, "this datatype is not yet resolved");
  Assert(t.isDatatype() && ((DatatypeType)t).getDatatype() == *this);
  ExprManagerScope ems(d_internal->getTypeNode().toType());
  TypeNode tn = TypeNode::fromType(t);
  return d_internal->getCardinality(tn);
}

Cardinality Datatype::getCardinality() const
{
  PrettyCheckArgument(!isParametric(), this, "for getCardinality, this datatype cannot be parametric");
  ExprManagerScope ems(d_internal->getTypeNode().toType());
  return d_internal->getCardinality();
}

bool Datatype::isRecursiveSingleton(Type t) const
{
  PrettyCheckArgument(isResolved(), this, "this datatype is not yet resolved");
  Assert(t.isDatatype() && ((DatatypeType)t).getDatatype() == *this);
  ExprManagerScope ems(d_internal->getTypeNode().toType());
  TypeNode tn = TypeNode::fromType(t);
  return d_internal->isRecursiveSingleton(tn);
}

bool Datatype::isRecursiveSingleton() const
{
  PrettyCheckArgument(!isParametric(), this, "for isRecursiveSingleton, this datatype cannot be parametric");
  ExprManagerScope ems(d_internal->getTypeNode().toType());
  return d_internal->isRecursiveSingleton();
}

unsigned Datatype::getNumRecursiveSingletonArgTypes(Type t) const
{
  Assert(isRecursiveSingleton(t));
  ExprManagerScope ems(d_internal->getTypeNode().toType());
  TypeNode tn = TypeNode::fromType(t);
  return d_internal->getNumRecursiveSingletonArgTypes(tn);
}

unsigned Datatype::getNumRecursiveSingletonArgTypes() const
{
  PrettyCheckArgument(!isParametric(), this, "for getNumRecursiveSingletonArgTypes, this datatype cannot be parametric");
  ExprManagerScope ems(d_internal->getTypeNode().toType());
  return d_internal->getNumRecursiveSingletonArgTypes();
}

Type Datatype::getRecursiveSingletonArgType(Type t, unsigned i) const
{
  Assert(isRecursiveSingleton(t));
  ExprManagerScope ems(d_internal->getTypeNode().toType());
  TypeNode tn = TypeNode::fromType(t);
  return d_internal->getRecursiveSingletonArgType(tn, i).toType();
}

Type Datatype::getRecursiveSingletonArgType(unsigned i) const
{
  PrettyCheckArgument(!isParametric(), this, "for getRecursiveSingletonArgType, this datatype cannot be parametric");
  ExprManagerScope ems(d_internal->getTypeNode().toType());
  return d_internal->getRecursiveSingletonArgType(i).toType();
}

bool Datatype::isFinite(Type t) const
{
  PrettyCheckArgument(isResolved(), this, "this datatype is not yet resolved");
  Assert(t.isDatatype() && ((DatatypeType)t).getDatatype() == *this); 
  ExprManagerScope ems(d_internal->getTypeNode().toType());
  TypeNode tn = TypeNode::fromType(t);
  return d_internal->isFinite(tn);
}
bool Datatype::isFinite() const
{
  PrettyCheckArgument(isResolved() && !isParametric(), this, "this datatype must be resolved and not parametric");
  return d_internal->isFinite();
}

bool Datatype::isInterpretedFinite(Type t) const
{
  PrettyCheckArgument(isResolved(), this, "this datatype is not yet resolved");
  Assert(t.isDatatype() && ((DatatypeType)t).getDatatype() == *this);
  ExprManagerScope ems(d_internal->getTypeNode().toType());
  TypeNode tn = TypeNode::fromType(t);
  return d_internal->isInterpretedFinite(tn);
}
bool Datatype::isInterpretedFinite() const
{
  PrettyCheckArgument(isResolved() && !isParametric(), this, "this datatype must be resolved and not parametric");
  ExprManagerScope ems(d_internal->getTypeNode().toType());
  return d_internal->isInterpretedFinite();
}

bool Datatype::isWellFounded() const
{
  ExprManagerScope ems(d_internal->getTypeNode().toType());
  return d_internal->isWellFounded();
}

Expr Datatype::mkGroundTerm(Type t) const
{
  PrettyCheckArgument(isResolved(), this, "this datatype is not yet resolved");
  ExprManagerScope ems(d_internal->getTypeNode().toType());
  TypeNode tn = TypeNode::fromType(t);
  return d_internal->mkGroundTerm(tn).toExpr();
}

Expr Datatype::mkGroundValue(Type t) const
{
  PrettyCheckArgument(isResolved(), this, "this datatype is not yet resolved");
  ExprManagerScope ems(d_internal->getTypeNode().toType());
  TypeNode tn = TypeNode::fromType(t);
  return d_internal->mkGroundValue(tn).toExpr();
}

DatatypeType Datatype::getDatatypeType() const
{
  PrettyCheckArgument(isResolved(), *this, "Datatype must be resolved to get its DatatypeType");
  ExprManagerScope ems(d_internal->getTypeNode().toType());
  Type self = d_internal->getTypeNode().toType();
  PrettyCheckArgument(!self.isNull(), *this);
  return DatatypeType(self);
}

DatatypeType Datatype::getDatatypeType(const std::vector<Type>& params) const
{
  PrettyCheckArgument(isResolved(), *this, "Datatype must be resolved to get its DatatypeType");
  ExprManagerScope ems(d_internal->getTypeNode().toType());
  Type self = d_internal->getTypeNode().toType();
  PrettyCheckArgument(!self.isNull() && DatatypeType(self).isParametric(), this);
  return DatatypeType(self).instantiate(params);
}

bool Datatype::operator==(const Datatype& other) const
{
  // two datatypes are == iff the name is the same and they have
  // exactly matching constructors (in the same order)

  if(this == &other) {
    return true;
  }

  if(isResolved() != other.isResolved()) {
    return false;
  }

  if( getName() != other.getName() ||
      getNumConstructors() != other.getNumConstructors() ) {
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
    Assert(isResolved() == !(*i).getConstructor().isNull()
           && isResolved() == !(*i).getTester().isNull()
           && (*i).getConstructor().isNull() == (*j).getConstructor().isNull()
           && (*i).getTester().isNull() == (*j).getTester().isNull());
    if(!(*i).getConstructor().isNull() && (*i).getConstructor() != (*j).getConstructor()) {
      return false;
    }
    if(!(*i).getTester().isNull() && (*i).getTester() != (*j).getTester()) {
      return false;
    }
    for(DatatypeConstructor::const_iterator k = (*i).begin(), l = (*j).begin(); k != (*i).end(); ++k, ++l) {
      Assert(l != (*j).end());
      if((*k).getName() != (*l).getName()) {
        return false;
      }
      // testing equivalence of selectors is harder b/c args might not
      // be resolved yet
      Assert(isResolved() == (*k).isResolved()
             && (*k).isResolved() == (*l).isResolved());
      if((*k).isResolved()) {
        // both are resolved, so simply compare the selectors directly
        if((*k).getSelector() != (*l).getSelector()) {
          return false;
        }
      } else {
        // neither is resolved, so compare their (possibly unresolved)
        // types; we don't know if they'll be resolved the same way,
        // so we can't ever say unresolved types are equal
        if(!(*k).getSelector().isNull() && !(*l).getSelector().isNull()) {
          if((*k).getSelector().getType() != (*l).getSelector().getType()) {
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

const DatatypeConstructor& Datatype::operator[](size_t index) const {
  PrettyCheckArgument(index < getNumConstructors(), index, "index out of bounds");
  return d_constructors[index];
}

const DatatypeConstructor& Datatype::operator[](std::string name) const {
  for(const_iterator i = begin(); i != end(); ++i) {
    if((*i).getName() == name) {
      return *i;
    }
  }
  std::string dname = getName();
  IllegalArgument(name, "No such constructor `%s' of datatype `%s'", name.c_str(), dname.c_str());
}

Expr Datatype::getConstructor(std::string name) const {
  return (*this)[name].getConstructor();
}

Type Datatype::getSygusType() const {
  return d_internal->getSygusType().toType();
}

Expr Datatype::getSygusVarList() const {
  return d_internal->getSygusVarList().toExpr();
}

bool Datatype::getSygusAllowConst() const {
  return d_internal->getSygusAllowConst();
}

bool Datatype::getSygusAllowAll() const {
  return d_internal->getSygusAllowAll();
}

bool Datatype::involvesExternalType() const{
  return d_internal->involvesExternalType();
}

bool Datatype::involvesUninterpretedType() const{
  return d_internal->involvesUninterpretedType();
}

const std::vector<DatatypeConstructor>* Datatype::getConstructors() const
{
  return &d_constructors;
}

DatatypeConstructor::DatatypeConstructor(std::string name)
    :  // We don't want to introduce a new data member, because eventually
       // we're going to be a constant stuffed inside a node.  So we stow
       // the tester name away inside the constructor name until
       // resolution. 
      d_internal(new DTypeConstructor(name,std::string("is_" + name),1))
{
  PrettyCheckArgument(name != "", name, "cannot construct a datatype constructor without a name");
}

DatatypeConstructor::DatatypeConstructor(std::string name,
                                         std::string tester,
                                         unsigned weight)
    :  // We don't want to introduce a new data member, because eventually
       // we're going to be a constant stuffed inside a node.  So we stow
       // the tester name away inside the constructor name until
       // resolution.
      d_internal(new DTypeConstructor(name, tester, weight))
{
  PrettyCheckArgument(name != "", name, "cannot construct a datatype constructor without a name");
  PrettyCheckArgument(!tester.empty(), tester, "cannot construct a datatype constructor without a tester");
}

void DatatypeConstructor::setSygus(Expr op,
                                   std::shared_ptr<SygusPrintCallback> spc)
{
  PrettyCheckArgument(
      !isResolved(), this, "cannot modify a finalized Datatype constructor");
  Node opn = Node::fromExpr(op);
  // FIXME
  std::shared_ptr<SygusPrintCallbackInternal> spci;
  d_internal->setSygus(op, spci);
  d_sygus_pc = spc;
}

const std::vector<DatatypeConstructorArg>* DatatypeConstructor::getArgs()
    const
{
  return &d_args;
}

void DatatypeConstructor::addArg(std::string selectorName, Type selectorType) {
  // We don't want to introduce a new data member, because eventually
  // we're going to be a constant stuffed inside a node.  So we stow
  // the selector type away inside a var until resolution (when we can
  // create the proper selector type)
  PrettyCheckArgument(!isResolved(), this, "cannot modify a finalized Datatype constructor");
  PrettyCheckArgument(!selectorType.isNull(), selectorType, "cannot add a null selector type");

  // we're using some internals, so we have to set up this library context
  ExprManagerScope ems(selectorType);

  Expr type = NodeManager::currentNM()->mkSkolem("unresolved_" + selectorName, TypeNode::fromType(selectorType), "is an unresolved selector type placeholder", NodeManager::SKOLEM_EXACT_NAME | NodeManager::SKOLEM_NO_NOTIFY).toExpr();
  Debug("datatypes") << type << endl;
  d_args.push_back(DatatypeConstructorArg(selectorName, type));
  d_internal->addArg(*d_args.back().d_internal);
}

void DatatypeConstructor::addArg(std::string selectorName, DatatypeUnresolvedType selectorType) {
  // We don't want to introduce a new data member, because eventually
  // we're going to be a constant stuffed inside a node.  So we stow
  // the selector type away after a NUL in the name string until
  // resolution (when we can create the proper selector type)
  PrettyCheckArgument(!isResolved(), this, "cannot modify a finalized Datatype constructor");
  PrettyCheckArgument(selectorType.getName() != "", selectorType, "cannot add a null selector type");
  d_args.push_back(DatatypeConstructorArg(selectorName + '\0' + selectorType.getName(), Expr()));
  d_internal->addArg(*d_args.back().d_internal);
}

void DatatypeConstructor::addArg(std::string selectorName, DatatypeSelfType) {
  // We don't want to introduce a new data member, because eventually
  // we're going to be a constant stuffed inside a node.  So we mark
  // the name string with a NUL to indicate that we have a
  // self-selecting selector until resolution (when we can create the
  // proper selector type)
  PrettyCheckArgument(!isResolved(), this, "cannot modify a finalized Datatype constructor");
  d_args.push_back(DatatypeConstructorArg(selectorName + '\0', Expr()));
  d_internal->addArg(*d_args.back().d_internal);
}

std::string DatatypeConstructor::getName() const
{
  std::string name = d_internal->getName();
  return name.substr(0, name.find('\0'));
}

std::string DatatypeConstructor::getTesterName() const
{
  std::string name = d_internal->getName();
  return name.substr(name.find('\0') + 1);
}

Expr DatatypeConstructor::getConstructor() const {
  PrettyCheckArgument(isResolved(), this, "this datatype constructor is not yet resolved");
  return d_internal->getConstructor().toExpr();
}

Type DatatypeConstructor::getSpecializedConstructorType(Type returnType) const {
  PrettyCheckArgument(isResolved(), this, "this datatype constructor is not yet resolved");
  PrettyCheckArgument(returnType.isDatatype(), this, "cannot get specialized constructor type for non-datatype type");
  ExprManagerScope ems(getConstructor());
  TypeNode tn = TypeNode::fromType(returnType);
  return d_internal->getSpecializedConstructorType(tn).toType();
}

Expr DatatypeConstructor::getTester() const {
  PrettyCheckArgument(isResolved(), this, "this datatype constructor is not yet resolved");
  return d_internal->getTester().toExpr();
}

Expr DatatypeConstructor::getSygusOp() const {
  PrettyCheckArgument(isResolved(), this, "this datatype constructor is not yet resolved");
  return d_internal->getSygusOp().toExpr();
}

bool DatatypeConstructor::isSygusIdFunc() const {
  PrettyCheckArgument(isResolved(), this, "this datatype constructor is not yet resolved");
  return d_internal->isSygusIdFunc();
}

unsigned DatatypeConstructor::getWeight() const
{
  PrettyCheckArgument(
      isResolved(), this, "this datatype constructor is not yet resolved");
  return d_internal->getWeight();
}

std::shared_ptr<SygusPrintCallback> DatatypeConstructor::getSygusPrintCallback() const
{
  PrettyCheckArgument(
      isResolved(), this, "this datatype constructor is not yet resolved");
  return d_sygus_pc;
}

Cardinality DatatypeConstructor::getCardinality(Type t) const
{
  PrettyCheckArgument(isResolved(), this, "this datatype constructor is not yet resolved");
  TypeNode tn = TypeNode::fromType(t);
  return d_internal->getCardinality(tn);
}

bool DatatypeConstructor::isFinite(Type t) const
{
  PrettyCheckArgument(isResolved(), this, "this datatype constructor is not yet resolved");
  ExprManagerScope ems(getConstructor());
  TypeNode tn = TypeNode::fromType(t);
  return d_internal->isFinite(tn);
}

bool DatatypeConstructor::isInterpretedFinite(Type t) const
{
  PrettyCheckArgument(isResolved(), this, "this datatype constructor is not yet resolved");
  ExprManagerScope ems(getConstructor());
  TypeNode tn = TypeNode::fromType(t);
  return d_internal->isInterpretedFinite(tn);
}

const DatatypeConstructorArg& DatatypeConstructor::operator[](size_t index) const {
  PrettyCheckArgument(index < getNumArgs(), index, "index out of bounds");
  return d_args[index];
}

const DatatypeConstructorArg& DatatypeConstructor::operator[](std::string name) const {
  for(const_iterator i = begin(); i != end(); ++i) {
    if((*i).getName() == name) {
      return *i;
    }
  }
  std::string dname = getName();
  IllegalArgument(name, "No such arg `%s' of constructor `%s'", name.c_str(), dname.c_str());
}

Expr DatatypeConstructor::getSelector(std::string name) const {
  return (*this)[name].getSelector();
}

Type DatatypeConstructor::getArgType(unsigned index) const
{
  PrettyCheckArgument(index < getNumArgs(), index, "index out of bounds");
  return d_internal->getArgType(index).toType();
}

bool DatatypeConstructor::involvesExternalType() const{
  return d_internal->involvesExternalType();
}

bool DatatypeConstructor::involvesUninterpretedType() const{
  return d_internal->involvesUninterpretedType();
}

DatatypeConstructorArg::DatatypeConstructorArg(std::string name, Expr selector) :
  d_internal(new DTypeConstructorArg(name,Node::fromExpr(selector))) {
  PrettyCheckArgument(name != "", name, "cannot construct a datatype constructor arg without a name");
}

std::string DatatypeConstructorArg::getName() const
{
  string name = d_internal->getName();
  const size_t nul = name.find('\0');
  if(nul != string::npos) {
    name.resize(nul);
  }
  return name;
}

Expr DatatypeConstructorArg::getSelector() const {
  PrettyCheckArgument(isResolved(), this, "cannot get a selector for an unresolved datatype constructor");
  return d_internal->getSelector().toExpr();
}

Expr DatatypeConstructor::getSelectorInternal( Type domainType, size_t index ) const {
  PrettyCheckArgument(isResolved(), this, "cannot get an internal selector for an unresolved datatype constructor");
  PrettyCheckArgument(index < getNumArgs(), index, "index out of bounds");
  TypeNode dtn = TypeNode::fromType(domainType);
  return d_internal->getSelectorInternal(dtn, index).toExpr();
}

int DatatypeConstructor::getSelectorIndexInternal( Expr sel ) const {
  PrettyCheckArgument(isResolved(), this, "cannot get an internal selector index for an unresolved datatype constructor");
  Node seln = Node::fromExpr(sel);
  return d_internal->getSelectorIndexInternal(seln);
}

Expr DatatypeConstructorArg::getConstructor() const {
  PrettyCheckArgument(isResolved(), this,
                "cannot get a associated constructor for argument of an unresolved datatype constructor");
  return d_internal->getConstructor().toExpr();
}

SelectorType DatatypeConstructorArg::getType() const {
  return getSelector().getType();
}

Type DatatypeConstructorArg::getRangeType() const {
  return getType().getRangeType();
}

bool DatatypeConstructorArg::isUnresolvedSelf() const
{
  std::string name = getName();
  return getSelector().isNull() && name.size() == name.find('\0') + 1;
}

bool DatatypeConstructorArg::isResolved() const
{
  // We could just write:
  //
  //   return !d_selector.isNull() && d_selector.getType().isSelector();
  //
  // HOWEVER, this causes problems in ExprManager tear-down, because
  // the attributes are removed before the pool is purged.  When the
  // pool is purged, this triggers an equality test between Datatypes,
  // and this triggers a call to isResolved(), which breaks because
  // d_selector has no type after attributes are stripped.
  //
  // This problem, coupled with the fact that this function is called
  // _often_, means we should just use a boolean flag.
  //
  return d_internal->isResolved();
}

std::ostream& operator<<(std::ostream& os, const Datatype& dt)
{
  // can only output datatypes in the CVC4 native language
  language::SetLanguage::Scope ls(os, language::output::LANG_CVC4);
  dt.toStream(os);
  return os;
}

void Datatype::toStream(std::ostream& out) const
{
  d_internal->toStream(out);
}

std::ostream& operator<<(std::ostream& os, const DatatypeConstructor& ctor) {
  // can only output datatypes in the CVC4 native language
  language::SetLanguage::Scope ls(os, language::output::LANG_CVC4);
  ctor.toStream(os);
  return os;
}

void DatatypeConstructor::toStream(std::ostream& out) const
{
  d_internal->toStream(out);
}

std::ostream& operator<<(std::ostream& os, const DatatypeConstructorArg& arg) {
  // can only output datatypes in the CVC4 native language
  language::SetLanguage::Scope ls(os, language::output::LANG_CVC4);
  arg.toStream(os);
  return os;
}

void DatatypeConstructorArg::toStream(std::ostream& out) const
{
  d_internal->toStream(out);
}

DatatypeIndexConstant::DatatypeIndexConstant(unsigned index) : d_index(index) {}
std::ostream& operator<<(std::ostream& out, const DatatypeIndexConstant& dic) {
  return out << "index_" << dic.getIndex();
}



std::string Datatype::getName() const { return d_internal->getName(); }
size_t Datatype::getNumConstructors() const
{
  return d_internal->getNumConstructors();
}

bool Datatype::isParametric() const { return d_internal->isParametric(); }
size_t Datatype::getNumParameters() const { return d_internal->getNumParameters(); }
Type Datatype::getParameter( unsigned int i ) const {
  CheckArgument(isParametric(), this,
                "Cannot get type parameter of a non-parametric datatype.");
  CheckArgument(i < getNumParameters(), i,
                "Type parameter index out of range for datatype.");
  return d_internal->getParameter(i).toType();
}

std::vector<Type> Datatype::getParameters() const {
  CheckArgument(isParametric(), this,
                "Cannot get type parameters of a non-parametric datatype.");
  std::vector<Type> params;
  std::vector<TypeNode > paramsn = d_internal->getParameters();
  // convert to type
  for (unsigned i=0, nparams = paramsn.size(); i<nparams; i++)
  {
    params.push_back(paramsn[i].toType());
  }
  return params;
}

bool Datatype::isCodatatype() const {
  return d_internal->isCodatatype();
}

bool Datatype::isSygus() const {
  return d_internal->isSygus();
}

bool Datatype::isTuple() const {
  return d_internal->isTuple();
}

bool Datatype::isRecord() const {
  return d_isRecord;
}

Record * Datatype::getRecord() const {
  return d_record;
}
bool Datatype::operator!=(const Datatype& other) const
{
  return !(*this == other);
}

bool Datatype::isResolved() const { return d_internal->isResolved(); }
Datatype::iterator Datatype::begin()
{
  return iterator(d_constructors, true);
}

Datatype::iterator Datatype::end()
{
  return iterator(d_constructors, false);
}

Datatype::const_iterator Datatype::begin() const
{
  return const_iterator(d_constructors, true);
}

Datatype::const_iterator Datatype::end() const
{
  return const_iterator(d_constructors, false);
}

bool DatatypeConstructor::isResolved() const
{
  return !getTester().isNull();
}

size_t DatatypeConstructor::getNumArgs() const { return d_args.size(); }

DatatypeConstructor::iterator DatatypeConstructor::begin()
{
  return iterator(d_args, true);
}

DatatypeConstructor::iterator DatatypeConstructor::end()
{
  return iterator(d_args, false);
}

DatatypeConstructor::const_iterator DatatypeConstructor::begin() const
{
  return const_iterator(d_args, true);
}

DatatypeConstructor::const_iterator DatatypeConstructor::end() const
{
  return const_iterator(d_args, false);
}
}/* CVC4 namespace */
