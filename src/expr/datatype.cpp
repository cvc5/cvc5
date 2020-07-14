/*********************                                                        */
/*! \file datatype.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Morgan Deters, Tim King
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
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
#include "expr/dtype.h"
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

using namespace std;

namespace CVC4 {

Datatype::~Datatype()
{
  ExprManagerScope ems(*d_em);
  d_internal.reset();
  d_constructors.clear();
}

Datatype::Datatype(ExprManager* em, std::string name, bool isCo)
    : d_em(em),
      d_internal(nullptr),
      d_record(NULL),
      d_isRecord(false),
      d_constructors()
{
  ExprManagerScope ems(*d_em);
  d_internal = std::make_shared<DType>(name, isCo);
}

Datatype::Datatype(ExprManager* em,
                   std::string name,
                   const std::vector<Type>& params,
                   bool isCo)
    : d_em(em),
      d_internal(nullptr),
      d_record(NULL),
      d_isRecord(false),
      d_constructors()
{
  ExprManagerScope ems(*d_em);
  std::vector<TypeNode> paramsn;
  for (const Type& t : params)
  {
    paramsn.push_back(TypeNode::fromType(t));
  }
  d_internal = std::make_shared<DType>(name, paramsn, isCo);
}

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
    Assert(n.hasAttribute(DTypeIndexAttr()));
    return n.getAttribute(DTypeIndexAttr());
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
    Assert(n.hasAttribute(DTypeConsIndexAttr()));
    return n.getAttribute(DTypeConsIndexAttr());
  }
}

void Datatype::resolve(const std::map<std::string, DatatypeType>& resolutions,
                       const std::vector<Type>& placeholders,
                       const std::vector<Type>& replacements,
                       const std::vector<SortConstructorType>& paramTypes,
                       const std::vector<DatatypeType>& paramReplacements)
{
  PrettyCheckArgument(!isResolved(), this, "cannot resolve a Datatype twice");
  PrettyCheckArgument(resolutions.find(getName()) != resolutions.end(),
                      resolutions,
                      "Datatype::resolve(): resolutions doesn't contain me!");
  PrettyCheckArgument(placeholders.size() == replacements.size(), placeholders,
                "placeholders and replacements must be the same size");
  PrettyCheckArgument(paramTypes.size() == paramReplacements.size(), paramTypes,
                "paramTypes and paramReplacements must be the same size");
  PrettyCheckArgument(getNumConstructors() > 0, *this, "cannot resolve a Datatype that has no constructors");

  // we're using some internals, so we have to make sure that the Datatype's
  // ExprManager is active
  ExprManagerScope ems(*d_em);

  Trace("datatypes") << "Datatype::resolve: " << getName()
                     << ", #placeholders=" << placeholders.size() << std::endl;

  std::map<std::string, TypeNode> resolutionsn;
  std::vector<TypeNode> placeholdersn;
  std::vector<TypeNode> replacementsn;
  std::vector<TypeNode> paramTypesn;
  std::vector<TypeNode> paramReplacementsn;
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
  bool res = d_internal->resolve(resolutionsn,
                                 placeholdersn,
                                 replacementsn,
                                 paramTypesn,
                                 paramReplacementsn);
  if (!res)
  {
    IllegalArgument(*this,
                    "could not resolve datatype that is not well formed");
  }
  Trace("dt-debug") << "Datatype::resolve: finished " << getName() << " "
                    << d_constructors.size() << std::endl;
  AlwaysAssert(isResolved());
  //
  d_self = d_internal->getTypeNode().toType();
  for (DatatypeConstructor& c : d_constructors)
  {
    AlwaysAssert(c.isResolved());
    c.d_constructor = c.d_internal->getConstructor().toExpr();
    for (size_t i = 0, nargs = c.getNumArgs(); i < nargs; i++)
    {
      AlwaysAssert(c.d_args[i].isResolved());
      c.d_args[i].d_selector = c.d_args[i].d_internal->getSelector().toExpr();
    }
  }

  if( d_isRecord ){
    std::vector< std::pair<std::string, Type> > fields;
    for( unsigned i=0; i<(*this)[0].getNumArgs(); i++ ){
      fields.push_back( std::pair<std::string, Type>( (*this)[0][i].getName(), (*this)[0][i].getRangeType() ) );
    }
    d_record.reset(new Record(fields));
  }
}

void Datatype::addConstructor(const DatatypeConstructor& c) {
  Trace("dt-debug") << "Datatype::addConstructor" << std::endl;
  PrettyCheckArgument(
      !isResolved(), this, "cannot add a constructor to a finalized Datatype");
  d_constructors.push_back(c);
  d_internal->addConstructor(c.d_internal);
  Trace("dt-debug") << "Datatype::addConstructor: finished" << std::endl;
}


void Datatype::setSygus( Type st, Expr bvl, bool allow_const, bool allow_all ){
  PrettyCheckArgument(
      !isResolved(), this, "cannot set sygus type to a finalized Datatype");
  // We can be in a case where the only rule specified was
  // (Constant T), in which case we have not yet added a constructor. We
  // ensure an arbitrary constant is added in this case. We additionally
  // add a constant if the grammar has only non-nullary constructors, since this
  // ensures the datatype is well-founded (see 3423).
  // Notice we only want to do this for sygus datatypes that are user-provided.
  // At the moment, the condition !allow_all implies the grammar is
  // user-provided and hence may require a default constant.
  // TODO (https://github.com/CVC4/cvc4-projects/issues/38):
  // In an API for SyGuS, it probably makes more sense for the user to
  // explicitly add the "any constant" constructor with a call instead of
  // passing a flag. This would make the block of code unnecessary.
  if (allow_const && !allow_all)
  {
    // if i don't already have a constant (0-ary constructor)
    bool hasConstant = false;
    for (unsigned i = 0, ncons = getNumConstructors(); i < ncons; i++)
    {
      if ((*this)[i].getNumArgs() == 0)
      {
        hasConstant = true;
        break;
      }
    }
    if (!hasConstant)
    {
      // add an arbitrary one
      Expr op = st.mkGroundTerm();
      std::stringstream cname;
      cname << op;
      std::vector<Type> cargs;
      addSygusConstructor(op, cname.str(), cargs);
    }
  }

  TypeNode stn = TypeNode::fromType(st);
  Node bvln = Node::fromExpr(bvl);
  d_internal->setSygus(stn, bvln, allow_const, allow_all);
}

void Datatype::addSygusConstructor(Expr op,
                                   const std::string& cname,
                                   const std::vector<Type>& cargs,
                                   int weight)
{
  // avoid name clashes
  std::stringstream ss;
  ss << getName() << "_" << getNumConstructors() << "_" << cname;
  std::string name = ss.str();
  unsigned cweight = weight >= 0 ? weight : (cargs.empty() ? 0 : 1);
  DatatypeConstructor c(name, cweight);
  c.setSygus(op);
  for( unsigned j=0; j<cargs.size(); j++ ){
    Debug("parser-sygus-debug") << "  arg " << j << " : " << cargs[j] << std::endl;
    std::stringstream sname;
    sname << name << "_" << j;
    c.addArg(sname.str(), cargs[j]);
  }
  addConstructor(c);
}

void Datatype::addSygusConstructor(Kind k,
                                   const std::string& cname,
                                   const std::vector<Type>& cargs,
                                   int weight)
{
  ExprManagerScope ems(*d_em);
  Expr op = d_em->operatorOf(k);
  addSygusConstructor(op, cname, cargs, weight);
}

void Datatype::setTuple() {
  PrettyCheckArgument(
      !isResolved(), this, "cannot set tuple to a finalized Datatype");
  d_internal->setTuple();
}

void Datatype::setRecord() {
  PrettyCheckArgument(
      !isResolved(), this, "cannot set record to a finalized Datatype");
  d_isRecord = true;
}

Cardinality Datatype::getCardinality(Type t) const
{
  PrettyCheckArgument(isResolved(), this, "this datatype is not yet resolved");
  Assert(t.isDatatype() && ((DatatypeType)t).getDatatype() == *this);
  ExprManagerScope ems(d_self);
  TypeNode tn = TypeNode::fromType(t);
  return d_internal->getCardinality(tn);
}

Cardinality Datatype::getCardinality() const
{
  PrettyCheckArgument(!isParametric(), this, "for getCardinality, this datatype cannot be parametric");
  ExprManagerScope ems(d_self);
  return d_internal->getCardinality();
}

bool Datatype::isRecursiveSingleton(Type t) const
{
  PrettyCheckArgument(isResolved(), this, "this datatype is not yet resolved");
  Assert(t.isDatatype() && ((DatatypeType)t).getDatatype() == *this);
  ExprManagerScope ems(d_self);
  TypeNode tn = TypeNode::fromType(t);
  return d_internal->isRecursiveSingleton(tn);
}

bool Datatype::isRecursiveSingleton() const
{
  PrettyCheckArgument(!isParametric(), this, "for isRecursiveSingleton, this datatype cannot be parametric");
  ExprManagerScope ems(d_self);
  return d_internal->isRecursiveSingleton();
}

unsigned Datatype::getNumRecursiveSingletonArgTypes(Type t) const
{
  Assert(isRecursiveSingleton(t));
  ExprManagerScope ems(d_self);
  TypeNode tn = TypeNode::fromType(t);
  return d_internal->getNumRecursiveSingletonArgTypes(tn);
}

unsigned Datatype::getNumRecursiveSingletonArgTypes() const
{
  PrettyCheckArgument(!isParametric(), this, "for getNumRecursiveSingletonArgTypes, this datatype cannot be parametric");
  ExprManagerScope ems(d_self);
  return d_internal->getNumRecursiveSingletonArgTypes();
}

Type Datatype::getRecursiveSingletonArgType(Type t, unsigned i) const
{
  Assert(isRecursiveSingleton(t));
  ExprManagerScope ems(d_self);
  TypeNode tn = TypeNode::fromType(t);
  return d_internal->getRecursiveSingletonArgType(tn, i).toType();
}

Type Datatype::getRecursiveSingletonArgType(unsigned i) const
{
  PrettyCheckArgument(!isParametric(), this, "for getRecursiveSingletonArgType, this datatype cannot be parametric");
  ExprManagerScope ems(d_self);
  return d_internal->getRecursiveSingletonArgType(i).toType();
}

bool Datatype::isFinite(Type t) const
{
  PrettyCheckArgument(isResolved(), this, "this datatype is not yet resolved");
  Assert(t.isDatatype() && ((DatatypeType)t).getDatatype() == *this);
  ExprManagerScope ems(d_self);
  TypeNode tn = TypeNode::fromType(t);
  return d_internal->isFinite(tn);
}
bool Datatype::isFinite() const
{
  PrettyCheckArgument(isResolved() && !isParametric(), this, "this datatype must be resolved and not parametric");
  ExprManagerScope ems(d_self);
  return d_internal->isFinite();
}

bool Datatype::isInterpretedFinite(Type t) const
{
  PrettyCheckArgument(isResolved(), this, "this datatype is not yet resolved");
  Assert(t.isDatatype() && ((DatatypeType)t).getDatatype() == *this);
  ExprManagerScope ems(d_self);
  TypeNode tn = TypeNode::fromType(t);
  return d_internal->isInterpretedFinite(tn);
}
bool Datatype::isInterpretedFinite() const
{
  PrettyCheckArgument(isResolved() && !isParametric(), this, "this datatype must be resolved and not parametric");
  ExprManagerScope ems(d_self);
  return d_internal->isInterpretedFinite();
}

bool Datatype::isWellFounded() const
{
  ExprManagerScope ems(d_self);
  return d_internal->isWellFounded();
}

bool Datatype::hasNestedRecursion() const
{
  ExprManagerScope ems(d_self);
  return d_internal->hasNestedRecursion();
}

Expr Datatype::mkGroundTerm(Type t) const
{
  PrettyCheckArgument(isResolved(), this, "this datatype is not yet resolved");
  ExprManagerScope ems(d_self);
  TypeNode tn = TypeNode::fromType(t);
  Node gterm = d_internal->mkGroundTerm(tn);
  PrettyCheckArgument(
      !gterm.isNull(),
      this,
      "datatype is not well-founded, cannot construct a ground term!");
  return gterm.toExpr();
}

Expr Datatype::mkGroundValue(Type t) const
{
  PrettyCheckArgument(isResolved(), this, "this datatype is not yet resolved");
  ExprManagerScope ems(d_self);
  TypeNode tn = TypeNode::fromType(t);
  Node gvalue = d_internal->mkGroundValue(tn);
  PrettyCheckArgument(
      !gvalue.isNull(),
      this,
      "datatype is not well-founded, cannot construct a ground value!");
  return gvalue.toExpr();
}

DatatypeType Datatype::getDatatypeType() const
{
  PrettyCheckArgument(isResolved(), *this, "Datatype must be resolved to get its DatatypeType");
  ExprManagerScope ems(d_self);
  Type self = d_internal->getTypeNode().toType();
  PrettyCheckArgument(!self.isNull(), *this);
  return DatatypeType(self);
}

DatatypeType Datatype::getDatatypeType(const std::vector<Type>& params) const
{
  PrettyCheckArgument(isResolved(), *this, "Datatype must be resolved to get its DatatypeType");
  ExprManagerScope ems(d_self);
  Type self = d_internal->getTypeNode().toType();
  PrettyCheckArgument(!self.isNull() && DatatypeType(self).isParametric(),
                      this);
  return DatatypeType(self).instantiate(params);
}

bool Datatype::operator==(const Datatype& other) const
{
  // two datatypes are == iff the name is the same and they have
  // exactly matching constructors (in the same order)

  if(this == &other) {
    return true;
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
  IllegalArgument(name,
                  "No such constructor `%s' of datatype `%s'",
                  name.c_str(),
                  dname.c_str());
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

DatatypeConstructor::DatatypeConstructor(std::string name, unsigned weight)
    : d_internal(nullptr)
{
  PrettyCheckArgument(name != "", name, "cannot construct a datatype constructor without a name");
  d_internal = std::make_shared<DTypeConstructor>(name, weight);
}

void DatatypeConstructor::setSygus(Expr op)
{
  PrettyCheckArgument(
      !isResolved(), this, "cannot modify a finalized Datatype constructor");
  Node opn = Node::fromExpr(op);
  d_internal->setSygus(op);
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
  d_internal->addArg(d_args.back().d_internal);
}

void DatatypeConstructor::addArg(std::string selectorName, DatatypeUnresolvedType selectorType) {
  // We don't want to introduce a new data member, because eventually
  // we're going to be a constant stuffed inside a node.  So we stow
  // the selector type away after a NUL in the name string until
  // resolution (when we can create the proper selector type)
  PrettyCheckArgument(!isResolved(), this, "cannot modify a finalized Datatype constructor");
  PrettyCheckArgument(selectorType.getName() != "", selectorType, "cannot add a null selector type");
  d_args.push_back(DatatypeConstructorArg(selectorName + '\0' + selectorType.getName(), Expr()));
  d_internal->addArg(d_args.back().d_internal);
}

void DatatypeConstructor::addArg(std::string selectorName, DatatypeSelfType) {
  // We don't want to introduce a new data member, because eventually
  // we're going to be a constant stuffed inside a node.  So we mark
  // the name string with a NUL to indicate that we have a
  // self-selecting selector until resolution (when we can create the
  // proper selector type)
  PrettyCheckArgument(!isResolved(), this, "cannot modify a finalized Datatype constructor");
  d_args.push_back(DatatypeConstructorArg(selectorName + '\0', Expr()));
  d_internal->addArg(d_args.back().d_internal);
}

std::string DatatypeConstructor::getName() const
{
  return d_internal->getName();
}

Expr DatatypeConstructor::getConstructor() const {
  PrettyCheckArgument(isResolved(), this, "this datatype constructor is not yet resolved");
  return d_constructor;
}

Type DatatypeConstructor::getSpecializedConstructorType(Type returnType) const {
  PrettyCheckArgument(isResolved(), this, "this datatype constructor is not yet resolved");
  PrettyCheckArgument(returnType.isDatatype(), this, "cannot get specialized constructor type for non-datatype type");
  ExprManagerScope ems(d_constructor);
  TypeNode tn = TypeNode::fromType(returnType);
  return d_internal->getSpecializedConstructorType(tn).toType();
}

Expr DatatypeConstructor::getTester() const {
  PrettyCheckArgument(isResolved(), this, "this datatype constructor is not yet resolved");
  ExprManagerScope ems(d_constructor);
  return d_internal->getTester().toExpr();
}

Expr DatatypeConstructor::getSygusOp() const {
  PrettyCheckArgument(isResolved(), this, "this datatype constructor is not yet resolved");
  ExprManagerScope ems(d_constructor);
  return d_internal->getSygusOp().toExpr();
}

bool DatatypeConstructor::isSygusIdFunc() const {
  PrettyCheckArgument(isResolved(), this, "this datatype constructor is not yet resolved");
  ExprManagerScope ems(d_constructor);
  return d_internal->isSygusIdFunc();
}

unsigned DatatypeConstructor::getWeight() const
{
  PrettyCheckArgument(
      isResolved(), this, "this datatype constructor is not yet resolved");
  ExprManagerScope ems(d_constructor);
  return d_internal->getWeight();
}

Cardinality DatatypeConstructor::getCardinality(Type t) const
{
  PrettyCheckArgument(isResolved(), this, "this datatype constructor is not yet resolved");
  ExprManagerScope ems(d_constructor);
  TypeNode tn = TypeNode::fromType(t);
  return d_internal->getCardinality(tn);
}

bool DatatypeConstructor::isFinite(Type t) const
{
  PrettyCheckArgument(isResolved(), this, "this datatype constructor is not yet resolved");
  ExprManagerScope ems(d_constructor);
  TypeNode tn = TypeNode::fromType(t);
  return d_internal->isFinite(tn);
}

bool DatatypeConstructor::isInterpretedFinite(Type t) const
{
  PrettyCheckArgument(isResolved(), this, "this datatype constructor is not yet resolved");
  ExprManagerScope ems(d_constructor);
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
  IllegalArgument(name,
                  "No such arg `%s' of constructor `%s'",
                  name.c_str(),
                  dname.c_str());
}

Expr DatatypeConstructor::getSelector(std::string name) const {
  return (*this)[name].d_selector;
}

Type DatatypeConstructor::getArgType(unsigned index) const
{
  PrettyCheckArgument(index < getNumArgs(), index, "index out of bounds");
  ExprManagerScope ems(d_constructor);
  return d_internal->getArgType(index).toType();
}

bool DatatypeConstructor::involvesExternalType() const{
  ExprManagerScope ems(d_constructor);
  return d_internal->involvesExternalType();
}

bool DatatypeConstructor::involvesUninterpretedType() const{
  ExprManagerScope ems(d_constructor);
  return d_internal->involvesUninterpretedType();
}

DatatypeConstructorArg::DatatypeConstructorArg(std::string name, Expr selector)
    : d_internal(nullptr)
{
  PrettyCheckArgument(name != "", name, "cannot construct a datatype constructor arg without a name");
  d_internal = std::make_shared<DTypeSelector>(name, Node::fromExpr(selector));
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
  return d_selector;
}

Expr DatatypeConstructor::getSelectorInternal( Type domainType, size_t index ) const {
  PrettyCheckArgument(isResolved(), this, "cannot get an internal selector for an unresolved datatype constructor");
  PrettyCheckArgument(index < getNumArgs(), index, "index out of bounds");
  ExprManagerScope ems(d_constructor);
  TypeNode dtn = TypeNode::fromType(domainType);
  return d_internal->getSelectorInternal(dtn, index).toExpr();
}

int DatatypeConstructor::getSelectorIndexInternal( Expr sel ) const {
  PrettyCheckArgument(isResolved(), this, "cannot get an internal selector index for an unresolved datatype constructor");
  ExprManagerScope ems(d_constructor);
  Node seln = Node::fromExpr(sel);
  return d_internal->getSelectorIndexInternal(seln);
}

Expr DatatypeConstructorArg::getConstructor() const {
  PrettyCheckArgument(isResolved(), this,
                "cannot get a associated constructor for argument of an unresolved datatype constructor");
  ExprManagerScope ems(d_selector);
  return d_internal->getConstructor().toExpr();
}

SelectorType DatatypeConstructorArg::getType() const {
  return d_selector.getType();
}

Type DatatypeConstructorArg::getRangeType() const {
  return getType().getRangeType();
}

bool DatatypeConstructorArg::isUnresolvedSelf() const
{
  return d_selector.isNull();
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
  out << "DATATYPE " << getName();
  if (isParametric())
  {
    out << '[';
    for (size_t i = 0; i < getNumParameters(); ++i)
    {
      if(i > 0) {
        out << ',';
      }
      out << getParameter(i);
    }
    out << ']';
  }
  out << " =" << endl;
  Datatype::const_iterator i = begin(), i_end = end();
  if(i != i_end) {
    out << "  ";
    do {
      out << *i << endl;
      if(++i != i_end) {
        out << "| ";
      }
    } while(i != i_end);
  }
  out << "END;" << endl;
}

std::ostream& operator<<(std::ostream& os, const DatatypeConstructor& ctor) {
  // can only output datatypes in the CVC4 native language
  language::SetLanguage::Scope ls(os, language::output::LANG_CVC4);
  ctor.toStream(os);
  return os;
}

void DatatypeConstructor::toStream(std::ostream& out) const
{
  out << getName();

  DatatypeConstructor::const_iterator i = begin(), i_end = end();
  if(i != i_end) {
    out << "(";
    do {
      out << *i;
      if(++i != i_end) {
        out << ", ";
      }
    } while(i != i_end);
    out << ")";
  }
}

std::ostream& operator<<(std::ostream& os, const DatatypeConstructorArg& arg) {
  // can only output datatypes in the CVC4 native language
  language::SetLanguage::Scope ls(os, language::output::LANG_CVC4);
  arg.toStream(os);
  return os;
}

void DatatypeConstructorArg::toStream(std::ostream& out) const
{
  std::string name = getName();
  out << name << ": ";

  Type t;
  if (isResolved())
  {
    t = getRangeType();
  }
  else if (d_selector.isNull())
  {
    string typeName = name.substr(name.find('\0') + 1);
    out << ((typeName == "") ? "[self]" : typeName);
    return;
  }
  else
  {
    t = d_selector.getType();
  }
  out << t;
}

DatatypeIndexConstant::DatatypeIndexConstant(unsigned index) : d_index(index) {}
std::ostream& operator<<(std::ostream& out, const DatatypeIndexConstant& dic) {
  return out << "index_" << dic.getIndex();
}


std::string Datatype::getName() const
{
  ExprManagerScope ems(*d_em);
  return d_internal->getName();
}
size_t Datatype::getNumConstructors() const { return d_constructors.size(); }

bool Datatype::isParametric() const
{
  ExprManagerScope ems(*d_em);
  return d_internal->isParametric();
}
size_t Datatype::getNumParameters() const
{
  ExprManagerScope ems(*d_em);
  return d_internal->getNumParameters();
}
Type Datatype::getParameter(unsigned int i) const
{
  CheckArgument(isParametric(),
                this,
                "Cannot get type parameter of a non-parametric datatype.");
  CheckArgument(i < getNumParameters(),
                i,
                "Type parameter index out of range for datatype.");
  ExprManagerScope ems(*d_em);
  return d_internal->getParameter(i).toType();
}

std::vector<Type> Datatype::getParameters() const
{
  CheckArgument(isParametric(),
                this,
                "Cannot get type parameters of a non-parametric datatype.");
  std::vector<Type> params;
  std::vector<TypeNode> paramsn = d_internal->getParameters();
  // convert to type
  for (unsigned i = 0, nparams = paramsn.size(); i < nparams; i++)
  {
    params.push_back(paramsn[i].toType());
  }
  return params;
}

bool Datatype::isCodatatype() const
{
  ExprManagerScope ems(*d_em);
  return d_internal->isCodatatype();
}

bool Datatype::isSygus() const
{
  ExprManagerScope ems(*d_em);
  return d_internal->isSygus();
}

bool Datatype::isTuple() const
{
  ExprManagerScope ems(*d_em);
  return d_internal->isTuple();
}

bool Datatype::isRecord() const { return d_isRecord; }

Record* Datatype::getRecord() const { return d_record.get(); }
bool Datatype::operator!=(const Datatype& other) const
{
  return !(*this == other);
}

bool Datatype::isResolved() const
{
  ExprManagerScope ems(*d_em);
  return d_internal->isResolved();
}
Datatype::iterator Datatype::begin() { return iterator(d_constructors, true); }

Datatype::iterator Datatype::end() { return iterator(d_constructors, false); }

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
  return d_internal->isResolved();
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
