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

#include "base/cvc4_assert.h"
#include "expr/attribute.h"
#include "expr/expr_manager.h"
#include "expr/expr_manager_scope.h"
#include "expr/matcher.h"
#include "expr/node.h"
#include "expr/node_manager.h"
#include "expr/type.h"
#include "options/set_language.h"
#include "options/datatypes_options.h"

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
    Unhandled("arg must be a datatype constructor, selector, or tester");
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
  PrettyCheckArgument(!d_resolved, this, "cannot resolve a Datatype twice");
  PrettyCheckArgument(resolutions.find(d_name) != resolutions.end(), resolutions,
                "Datatype::resolve(): resolutions doesn't contain me!");
  PrettyCheckArgument(placeholders.size() == replacements.size(), placeholders,
                "placeholders and replacements must be the same size");
  PrettyCheckArgument(paramTypes.size() == paramReplacements.size(), paramTypes,
                "paramTypes and paramReplacements must be the same size");
  PrettyCheckArgument(getNumConstructors() > 0, *this, "cannot resolve a Datatype that has no constructors");
  DatatypeType self = (*resolutions.find(d_name)).second;
  PrettyCheckArgument(&self.getDatatype() == this, resolutions, "Datatype::resolve(): resolutions doesn't contain me!");
  d_resolved = true;
  size_t index = 0;
  for(std::vector<DatatypeConstructor>::iterator i = d_constructors.begin(), i_end = d_constructors.end(); i != i_end; ++i) {
    (*i).resolve(em, self, resolutions, placeholders, replacements, paramTypes, paramReplacements, index);
    Node::fromExpr((*i).d_constructor).setAttribute(DatatypeIndexAttr(), index);
    Node::fromExpr((*i).d_tester).setAttribute(DatatypeIndexAttr(), index++);
  }
  d_self = self;

  d_involvesExt =  false;
  d_involvesUt =  false;
  for(const_iterator i = begin(); i != end(); ++i) {
    if( (*i).involvesExternalType() ){
      d_involvesExt =  true;
    }
    if( (*i).involvesUninterpretedType() ){
      d_involvesUt =  true;
    }
  }

  if( d_isRecord ){
    std::vector< std::pair<std::string, Type> > fields;
    for( unsigned i=0; i<(*this)[0].getNumArgs(); i++ ){
      fields.push_back( std::pair<std::string, Type>( (*this)[0][i].getName(), (*this)[0][i].getRangeType() ) );
    }
    d_record = new Record(fields);
  }
}

void Datatype::addConstructor(const DatatypeConstructor& c) {
  PrettyCheckArgument(!d_resolved, this,
                "cannot add a constructor to a finalized Datatype");
  d_constructors.push_back(c);
}


void Datatype::setSygus( Type st, Expr bvl, bool allow_const, bool allow_all ){
  PrettyCheckArgument(!d_resolved, this,
                      "cannot set sygus type to a finalized Datatype");        
  d_sygus_type = st;
  d_sygus_bvl = bvl;
  d_sygus_allow_const = allow_const || allow_all;
  d_sygus_allow_all = allow_all;
}

void Datatype::addSygusConstructor(Expr op,
                                   const std::string& cname,
                                   const std::vector<Type>& cargs,
                                   std::shared_ptr<SygusPrintCallback> spc,
                                   int weight)
{
  Debug("dt-sygus") << "--> Add constructor " << cname << " to " << getName() << std::endl;
  Debug("dt-sygus") << "    sygus op : " << op << std::endl;
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
  PrettyCheckArgument(!d_resolved, this, "cannot set tuple to a finalized Datatype");
  d_isTuple = true;
}

void Datatype::setRecord() {
  PrettyCheckArgument(!d_resolved, this, "cannot set record to a finalized Datatype");
  d_isRecord = true;
}

Cardinality Datatype::getCardinality(Type t) const
{
  PrettyCheckArgument(isResolved(), this, "this datatype is not yet resolved");
  Assert( t.isDatatype() && ((DatatypeType)t).getDatatype()==*this );
  std::vector< Type > processing;
  computeCardinality( t, processing );
  return d_card;
}

Cardinality Datatype::getCardinality() const
{
  PrettyCheckArgument(!isParametric(), this, "for getCardinality, this datatype cannot be parametric");
  return getCardinality( d_self );
}

Cardinality Datatype::computeCardinality(Type t,
                                         std::vector<Type>& processing) const
{
  PrettyCheckArgument(isResolved(), this, "this datatype is not yet resolved");
  if( std::find( processing.begin(), processing.end(), d_self )!=processing.end() ){
    d_card = Cardinality::INTEGERS;
  }else{
    processing.push_back( d_self );
    Cardinality c = 0;
    for(const_iterator i = begin(), i_end = end(); i != i_end; ++i) {
      c += (*i).computeCardinality( t, processing );
    }
    d_card = c;
    processing.pop_back();
  }
  return d_card;
}

bool Datatype::isRecursiveSingleton(Type t) const
{
  PrettyCheckArgument(isResolved(), this, "this datatype is not yet resolved");
  Assert( t.isDatatype() && ((DatatypeType)t).getDatatype()==*this );
  if( d_card_rec_singleton.find( t )==d_card_rec_singleton.end() ){
    if( isCodatatype() ){
      Assert( d_card_u_assume[t].empty() );
      std::vector< Type > processing;
      if( computeCardinalityRecSingleton( t, processing, d_card_u_assume[t] ) ){
        d_card_rec_singleton[t] = 1;
      }else{
        d_card_rec_singleton[t] = -1;
      }
      if( d_card_rec_singleton[t]==1 ){
        Trace("dt-card") << "Datatype " << getName() << " is recursive singleton, dependent upon " << d_card_u_assume[t].size() << " uninterpreted sorts: " << std::endl;
        for( unsigned i=0; i<d_card_u_assume[t].size(); i++ ){
          Trace("dt-card") << "  " << d_card_u_assume[t][i] << std::endl;
        }
        Trace("dt-card") << std::endl;
      }
    }else{
      d_card_rec_singleton[t] = -1;
    }
  }
  return d_card_rec_singleton[t]==1;
}

bool Datatype::isRecursiveSingleton() const
{
  PrettyCheckArgument(!isParametric(), this, "for isRecursiveSingleton, this datatype cannot be parametric");
  return isRecursiveSingleton( d_self );
}

unsigned Datatype::getNumRecursiveSingletonArgTypes(Type t) const
{
  Assert( d_card_rec_singleton.find( t )!=d_card_rec_singleton.end() );
  Assert( isRecursiveSingleton( t ) );
  return d_card_u_assume[t].size();
}

unsigned Datatype::getNumRecursiveSingletonArgTypes() const
{
  PrettyCheckArgument(!isParametric(), this, "for getNumRecursiveSingletonArgTypes, this datatype cannot be parametric");
  return getNumRecursiveSingletonArgTypes( d_self );
}

Type Datatype::getRecursiveSingletonArgType(Type t, unsigned i) const
{
  Assert( d_card_rec_singleton.find( t )!=d_card_rec_singleton.end() );
  Assert( isRecursiveSingleton( t ) );
  return d_card_u_assume[t][i];
}

Type Datatype::getRecursiveSingletonArgType(unsigned i) const
{
  PrettyCheckArgument(!isParametric(), this, "for getRecursiveSingletonArgType, this datatype cannot be parametric");
  return getRecursiveSingletonArgType( d_self, i );
}

bool Datatype::computeCardinalityRecSingleton(Type t,
                                              std::vector<Type>& processing,
                                              std::vector<Type>& u_assume) const
{
  if( std::find( processing.begin(), processing.end(), d_self )!=processing.end() ){
    return true;
  }else{
    if( d_card_rec_singleton[t]==0 ){
      //if not yet computed
      if( d_constructors.size()==1 ){
        bool success = false;
        processing.push_back( d_self );
        for(unsigned i = 0; i<d_constructors[0].getNumArgs(); i++ ) {
          Type tc = ((SelectorType)d_constructors[0][i].getType()).getRangeType();
          //if it is an uninterpreted sort, then we depend on it having cardinality one
          if( tc.isSort() ){
            if( std::find( u_assume.begin(), u_assume.end(), tc )==u_assume.end() ){
              u_assume.push_back( tc );
            }
          //if it is a datatype, recurse
          }else if( tc.isDatatype() ){
            const Datatype & dt = ((DatatypeType)tc).getDatatype();
            if( !dt.computeCardinalityRecSingleton( t, processing, u_assume ) ){
              return false;
            }else{
              success = true;
            }
          //if it is a builtin type, it must have cardinality one
          }else if( !tc.getCardinality().isOne() ){
            return false;
          }
        }
        processing.pop_back();
        return success;
      }else{
        return false;
      }
    }else if( d_card_rec_singleton[t]==-1 ){
      return false;
    }else{
      for( unsigned i=0; i<d_card_u_assume[t].size(); i++ ){
        if( std::find( u_assume.begin(), u_assume.end(), d_card_u_assume[t][i] )==u_assume.end() ){
          u_assume.push_back( d_card_u_assume[t][i] );
        }
      }
      return true;
    }
  }
}

bool Datatype::isFinite(Type t) const
{
  PrettyCheckArgument(isResolved(), this, "this datatype is not yet resolved");
  Assert( t.isDatatype() && ((DatatypeType)t).getDatatype()==*this );

  // we're using some internals, so we have to set up this library context
  ExprManagerScope ems(d_self);
  TypeNode self = TypeNode::fromType(d_self);
  // is this already in the cache ?
  if(self.getAttribute(DatatypeFiniteComputedAttr())) {
    return self.getAttribute(DatatypeFiniteAttr());
  }
  for(const_iterator i = begin(), i_end = end(); i != i_end; ++i) {
    if(! (*i).isFinite( t )) {
      self.setAttribute(DatatypeFiniteComputedAttr(), true);
      self.setAttribute(DatatypeFiniteAttr(), false);
      return false;
    }
  }
  self.setAttribute(DatatypeFiniteComputedAttr(), true);
  self.setAttribute(DatatypeFiniteAttr(), true);
  return true;
}
bool Datatype::isFinite() const
{
  PrettyCheckArgument(isResolved() && !isParametric(), this, "this datatype must be resolved and not parametric");
  return isFinite( d_self );
}

bool Datatype::isInterpretedFinite(Type t) const
{
  PrettyCheckArgument(isResolved(), this, "this datatype is not yet resolved");
  Assert( t.isDatatype() && ((DatatypeType)t).getDatatype()==*this );
  // we're using some internals, so we have to set up this library context
  ExprManagerScope ems(d_self);
  TypeNode self = TypeNode::fromType(d_self);
  // is this already in the cache ?
  if(self.getAttribute(DatatypeUFiniteComputedAttr())) {
    return self.getAttribute(DatatypeUFiniteAttr());
  }
  //start by assuming it is not
  self.setAttribute(DatatypeUFiniteComputedAttr(), true);
  self.setAttribute(DatatypeUFiniteAttr(), false);
  for(const_iterator i = begin(), i_end = end(); i != i_end; ++i) {
    if(! (*i).isInterpretedFinite( t )) {
      return false;
    }
  }
  self.setAttribute(DatatypeUFiniteComputedAttr(), true);
  self.setAttribute(DatatypeUFiniteAttr(), true);
  return true;
}
bool Datatype::isInterpretedFinite() const
{
  PrettyCheckArgument(isResolved() && !isParametric(), this, "this datatype must be resolved and not parametric");
  return isInterpretedFinite( d_self );
}

bool Datatype::isWellFounded() const
{
  PrettyCheckArgument(isResolved(), this, "this datatype is not yet resolved");
  if( d_well_founded==0 ){
    // we're using some internals, so we have to set up this library context
    ExprManagerScope ems(d_self);
    std::vector< Type > processing;
    if( computeWellFounded( processing ) ){
      d_well_founded = 1;
    }else{
      d_well_founded = -1;
    }
  }
  return d_well_founded==1;
}

bool Datatype::computeWellFounded(std::vector<Type>& processing) const
{
  PrettyCheckArgument(isResolved(), this, "this datatype is not yet resolved");
  if( std::find( processing.begin(), processing.end(), d_self )!=processing.end() ){
    return d_isCo;
  }else{
    processing.push_back( d_self );
    for(const_iterator i = begin(), i_end = end(); i != i_end; ++i) {
      if( (*i).computeWellFounded( processing ) ){
        processing.pop_back();
        return true;
      }else{
        Trace("dt-wf") << "Constructor " << (*i).getName() << " is not well-founded." << std::endl;
      }
    }
    processing.pop_back();
    Trace("dt-wf") << "Datatype " << getName() << " is not well-founded." << std::endl;
    return false;
  }
}

Expr Datatype::mkGroundTerm(Type t) const
{
  PrettyCheckArgument(isResolved(), this, "this datatype is not yet resolved");
  ExprManagerScope ems(d_self);
  Debug("datatypes") << "mkGroundTerm of type " << t << std::endl;
  // is this already in the cache ?
  std::map< Type, Expr >::iterator it = d_ground_term.find( t );
  if( it != d_ground_term.end() ){
    Debug("datatypes") << "\nin cache: " << d_self << " => " << it->second << std::endl;
    return it->second;
  } else {
    std::vector< Type > processing;
    Expr groundTerm = computeGroundTerm( t, processing );
    if(!groundTerm.isNull() ) {
      // we found a ground-term-constructing constructor!
      d_ground_term[t] = groundTerm;
      Debug("datatypes") << "constructed: " << getName() << " => " << groundTerm << std::endl;
    }
    if( groundTerm.isNull() ){
      if( !d_isCo ){
        // if we get all the way here, we aren't well-founded
        IllegalArgument(*this, "datatype is not well-founded, cannot construct a ground term!");
      }else{
        return groundTerm;
      }
    }else{
      return groundTerm;
    }
  }
}

Expr getSubtermWithType( Expr e, Type t, bool isTop ){
  if( !isTop && e.getType()==t ){
    return e;
  }else{
    for( unsigned i=0; i<e.getNumChildren(); i++ ){
      Expr se = getSubtermWithType( e[i], t, false );
      if( !se.isNull() ){
        return se;
      }
    }
    return Expr();
  }
}

Expr Datatype::computeGroundTerm(Type t, std::vector<Type>& processing) const
{
  if( std::find( processing.begin(), processing.end(), t )==processing.end() ){
    processing.push_back( t );
    for( unsigned r=0; r<2; r++ ){
      for(const_iterator i = begin(), i_end = end(); i != i_end; ++i) {
        //do nullary constructors first
        if( ((*i).getNumArgs()==0)==(r==0)){
          Debug("datatypes") << "Try constructing for " << (*i).getName() << ", processing = " << processing.size() << std::endl;
          Expr e = (*i).computeGroundTerm( t, processing, d_ground_term );
          if( !e.isNull() ){
            //must check subterms for the same type to avoid infinite loops in type enumeration
            Expr se = getSubtermWithType( e, t, true );
            if( !se.isNull() ){
              Debug("datatypes") << "Take subterm " << se << std::endl;
              e = se;
            }
            processing.pop_back();
            return e;
          }else{
            Debug("datatypes") << "...failed." << std::endl;
          }
        }
      }
    }
    processing.pop_back();
  }else{
    Debug("datatypes") << "...already processing " << t << " " << d_self << std::endl;
  }
  return Expr();
}

DatatypeType Datatype::getDatatypeType() const
{
  PrettyCheckArgument(isResolved(), *this, "Datatype must be resolved to get its DatatypeType");
  PrettyCheckArgument(!d_self.isNull(), *this);
  return DatatypeType(d_self);
}

DatatypeType Datatype::getDatatypeType(const std::vector<Type>& params) const
{
  PrettyCheckArgument(isResolved(), *this, "Datatype must be resolved to get its DatatypeType");
  PrettyCheckArgument(!d_self.isNull() && DatatypeType(d_self).isParametric(), this);
  return DatatypeType(d_self).instantiate(params);
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

  if( d_name != other.d_name ||
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
    for(DatatypeConstructor::const_iterator k = (*i).begin(), l = (*j).begin(); k != (*i).end(); ++k, ++l) {
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
  IllegalArgument(name, "No such constructor `%s' of datatype `%s'", name.c_str(), d_name.c_str());
}


Expr Datatype::getSharedSelector( Type dtt, Type t, unsigned index ) const{
  PrettyCheckArgument(isResolved(), this, "this datatype is not yet resolved");
  std::map< Type, std::map< Type, std::map< unsigned, Expr > > >::iterator itd = d_shared_sel.find( dtt );
  if( itd!=d_shared_sel.end() ){
    std::map< Type, std::map< unsigned, Expr > >::iterator its = itd->second.find( t );
    if( its!=itd->second.end() ){
      std::map< unsigned, Expr >::iterator it = its->second.find( index );
      if( it!=its->second.end() ){
        return it->second;
      }
    }
  }
  //make the shared selector
  Expr s;
  NodeManager* nm = NodeManager::fromExprManager( d_self.getExprManager() );
  std::stringstream ss;
  ss << "sel_" << index;
  s = nm->mkSkolem(ss.str(), nm->mkSelectorType(TypeNode::fromType(dtt), TypeNode::fromType(t)), "is a shared selector", NodeManager::SKOLEM_NO_NOTIFY).toExpr();
  d_shared_sel[dtt][t][index] = s;
  Trace("dt-shared-sel") << "Made " << s << " of type " << dtt << " -> " << t << std::endl;
  return s; 
}

Expr Datatype::getConstructor(std::string name) const {
  return (*this)[name].getConstructor();
}

Type Datatype::getSygusType() const {
  return d_sygus_type;
}

Expr Datatype::getSygusVarList() const {
  return d_sygus_bvl;
}

bool Datatype::getSygusAllowConst() const {
  return d_sygus_allow_const;
}

bool Datatype::getSygusAllowAll() const {
  return d_sygus_allow_all;
}

bool Datatype::involvesExternalType() const{
  return d_involvesExt;
}

bool Datatype::involvesUninterpretedType() const{
  return d_involvesUt;
}

const std::vector<DatatypeConstructor>* Datatype::getConstructors() const
{
  return &d_constructors;
}

void DatatypeConstructor::resolve(ExprManager* em, DatatypeType self,
                                  const std::map<std::string, DatatypeType>& resolutions,
                                  const std::vector<Type>& placeholders,
                                  const std::vector<Type>& replacements,
                                  const std::vector< SortConstructorType >& paramTypes,
                                  const std::vector< DatatypeType >& paramReplacements, size_t cindex)
{
  PrettyCheckArgument(em != NULL, em, "cannot resolve a Datatype with a NULL expression manager");
  PrettyCheckArgument(!isResolved(),
                "cannot resolve a Datatype constructor twice; "
                "perhaps the same constructor was added twice, "
                "or to two datatypes?");

  // we're using some internals, so we have to set up this library context
  ExprManagerScope ems(*em);

  NodeManager* nm = NodeManager::fromExprManager(em);
  TypeNode selfTypeNode = TypeNode::fromType(self);
  size_t index = 0;
  for(std::vector<DatatypeConstructorArg>::iterator i = d_args.begin(), i_end = d_args.end(); i != i_end; ++i) {
    if((*i).d_selector.isNull()) {
      // the unresolved type wasn't created here; do name resolution
      string typeName = (*i).d_name.substr((*i).d_name.find('\0') + 1);
      (*i).d_name.resize((*i).d_name.find('\0'));
      if(typeName == "") {
        (*i).d_selector = nm->mkSkolem((*i).d_name, nm->mkSelectorType(selfTypeNode, selfTypeNode), "is a selector", NodeManager::SKOLEM_EXACT_NAME | NodeManager::SKOLEM_NO_NOTIFY).toExpr();
      } else {
        map<string, DatatypeType>::const_iterator j = resolutions.find(typeName);
        if(j == resolutions.end()) {
          stringstream msg;
          msg << "cannot resolve type \"" << typeName << "\" "
              << "in selector \"" << (*i).d_name << "\" "
              << "of constructor \"" << d_name << "\"";
          throw DatatypeResolutionException(msg.str());
        } else {
          (*i).d_selector = nm->mkSkolem((*i).d_name, nm->mkSelectorType(selfTypeNode, TypeNode::fromType((*j).second)), "is a selector", NodeManager::SKOLEM_EXACT_NAME | NodeManager::SKOLEM_NO_NOTIFY).toExpr();
        }
      }
    } else {
      // the type for the selector already exists; may need
      // complex-type substitution
      Type range = (*i).d_selector.getType();
      if(!placeholders.empty()) {
        range = range.substitute(placeholders, replacements);
      }
      if(!paramTypes.empty() ) {
        range = doParametricSubstitution( range, paramTypes, paramReplacements );
      }
      (*i).d_selector = nm->mkSkolem((*i).d_name, nm->mkSelectorType(selfTypeNode, TypeNode::fromType(range)), "is a selector", NodeManager::SKOLEM_EXACT_NAME | NodeManager::SKOLEM_NO_NOTIFY).toExpr();
    }
    Node::fromExpr((*i).d_selector).setAttribute(DatatypeConsIndexAttr(), cindex);
    Node::fromExpr((*i).d_selector).setAttribute(DatatypeIndexAttr(), index++);
    (*i).d_resolved = true;
  }

  Assert(index == getNumArgs());

  // Set constructor/tester last, since DatatypeConstructor::isResolved()
  // returns true when d_tester is not the null Expr.  If something
  // fails above, we want Constuctor::isResolved() to remain "false".
  // Further, mkConstructorType() iterates over the selectors, so
  // should get the results of any resolutions we did above.
  d_tester = nm->mkSkolem(getTesterName(), nm->mkTesterType(selfTypeNode), "is a tester", NodeManager::SKOLEM_EXACT_NAME | NodeManager::SKOLEM_NO_NOTIFY).toExpr();
  d_constructor = nm->mkSkolem(getName(), nm->mkConstructorType(*this, selfTypeNode), "is a constructor", NodeManager::SKOLEM_EXACT_NAME | NodeManager::SKOLEM_NO_NOTIFY).toExpr();
  // associate constructor with all selectors
  for(std::vector<DatatypeConstructorArg>::iterator i = d_args.begin(), i_end = d_args.end(); i != i_end; ++i) {
    (*i).d_constructor = d_constructor;
  }
}

Type DatatypeConstructor::doParametricSubstitution( Type range,
                                  const std::vector< SortConstructorType >& paramTypes,
                                  const std::vector< DatatypeType >& paramReplacements ) {
  TypeNode typn = TypeNode::fromType( range );
  if(typn.getNumChildren() == 0) {
    return range;
  } else {
    std::vector< Type > origChildren;
    std::vector< Type > children;
    for(TypeNode::const_iterator i = typn.begin(), iend = typn.end();i != iend; ++i) {
      origChildren.push_back( (*i).toType() );
      children.push_back( doParametricSubstitution( (*i).toType(), paramTypes, paramReplacements ) );
    }
    for( unsigned i = 0; i < paramTypes.size(); ++i ) {
      if( paramTypes[i].getArity() == origChildren.size() ) {
        Type tn = paramTypes[i].instantiate( origChildren );
        if( range == tn ) {
          return paramReplacements[i].instantiate( children );
        }
      }
    }
    NodeBuilder<> nb(typn.getKind());
    for( unsigned i = 0; i < children.size(); ++i ) {
      nb << TypeNode::fromType( children[i] );
    }
    return nb.constructTypeNode().toType();
  }
}

DatatypeConstructor::DatatypeConstructor(std::string name)
    :  // We don't want to introduce a new data member, because eventually
       // we're going to be a constant stuffed inside a node.  So we stow
       // the tester name away inside the constructor name until
       // resolution.
      d_name(name + '\0' + "is_" + name),  // default tester name is "is_FOO"
      d_tester(),
      d_args(),
      d_sygus_pc(nullptr),
      d_weight(1)
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
      d_name(name + '\0' + tester),
      d_tester(),
      d_args(),
      d_sygus_pc(nullptr),
      d_weight(weight)
{
  PrettyCheckArgument(name != "", name, "cannot construct a datatype constructor without a name");
  PrettyCheckArgument(!tester.empty(), tester, "cannot construct a datatype constructor without a tester");
}

void DatatypeConstructor::setSygus(Expr op,
                                   std::shared_ptr<SygusPrintCallback> spc)
{
  PrettyCheckArgument(
      !isResolved(), this, "cannot modify a finalized Datatype constructor");
  d_sygus_op = op;
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
}

void DatatypeConstructor::addArg(std::string selectorName, DatatypeUnresolvedType selectorType) {
  // We don't want to introduce a new data member, because eventually
  // we're going to be a constant stuffed inside a node.  So we stow
  // the selector type away after a NUL in the name string until
  // resolution (when we can create the proper selector type)
  PrettyCheckArgument(!isResolved(), this, "cannot modify a finalized Datatype constructor");
  PrettyCheckArgument(selectorType.getName() != "", selectorType, "cannot add a null selector type");
  d_args.push_back(DatatypeConstructorArg(selectorName + '\0' + selectorType.getName(), Expr()));
}

void DatatypeConstructor::addArg(std::string selectorName, DatatypeSelfType) {
  // We don't want to introduce a new data member, because eventually
  // we're going to be a constant stuffed inside a node.  So we mark
  // the name string with a NUL to indicate that we have a
  // self-selecting selector until resolution (when we can create the
  // proper selector type)
  PrettyCheckArgument(!isResolved(), this, "cannot modify a finalized Datatype constructor");
  d_args.push_back(DatatypeConstructorArg(selectorName + '\0', Expr()));
}

std::string DatatypeConstructor::getName() const
{
  return d_name.substr(0, d_name.find('\0'));
}

std::string DatatypeConstructor::getTesterName() const
{
  return d_name.substr(d_name.find('\0') + 1);
}

Expr DatatypeConstructor::getConstructor() const {
  PrettyCheckArgument(isResolved(), this, "this datatype constructor is not yet resolved");
  return d_constructor;
}

Type DatatypeConstructor::getSpecializedConstructorType(Type returnType) const {
  PrettyCheckArgument(isResolved(), this, "this datatype constructor is not yet resolved");
  PrettyCheckArgument(returnType.isDatatype(), this, "cannot get specialized constructor type for non-datatype type");
  ExprManagerScope ems(d_constructor);
  const Datatype& dt = Datatype::datatypeOf(d_constructor);
  PrettyCheckArgument(dt.isParametric(), this, "this datatype constructor is not parametric");
  DatatypeType dtt = dt.getDatatypeType();
  Matcher m(dtt);
  m.doMatching( TypeNode::fromType(dtt), TypeNode::fromType(returnType) );
  vector<Type> subst;
  m.getMatches(subst);
  vector<Type> params = dt.getParameters();
  return d_constructor.getType().substitute(params, subst);
}

Expr DatatypeConstructor::getTester() const {
  PrettyCheckArgument(isResolved(), this, "this datatype constructor is not yet resolved");
  return d_tester;
}

Expr DatatypeConstructor::getSygusOp() const {
  PrettyCheckArgument(isResolved(), this, "this datatype constructor is not yet resolved");
  return d_sygus_op;
}

bool DatatypeConstructor::isSygusIdFunc() const {
  PrettyCheckArgument(isResolved(), this, "this datatype constructor is not yet resolved");
  return (d_sygus_op.getKind() == kind::LAMBDA
          && d_sygus_op[0].getNumChildren() == 1
          && d_sygus_op[0][0] == d_sygus_op[1]);
}

unsigned DatatypeConstructor::getWeight() const
{
  PrettyCheckArgument(
      isResolved(), this, "this datatype constructor is not yet resolved");
  return d_weight;
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

  Cardinality c = 1;

  for(const_iterator i = begin(), i_end = end(); i != i_end; ++i) {
    c *= SelectorType((*i).getSelector().getType()).getRangeType().getCardinality();
  }

  return c;
}

/** compute the cardinality of this datatype */
Cardinality DatatypeConstructor::computeCardinality(
    Type t, std::vector<Type>& processing) const
{
  Cardinality c = 1;
  std::vector< Type > instTypes;
  std::vector< Type > paramTypes;
  if( DatatypeType(t).isParametric() ){
    paramTypes = DatatypeType(t).getDatatype().getParameters();
    instTypes = DatatypeType(t).getParamTypes();
  }  
  for(const_iterator i = begin(), i_end = end(); i != i_end; ++i) {
    Type tc = SelectorType((*i).getSelector().getType()).getRangeType();
    if( DatatypeType(t).isParametric() ){
      tc = tc.substitute( paramTypes, instTypes );
    }
    if( tc.isDatatype() ){
      const Datatype& dt = ((DatatypeType)tc).getDatatype();
      c *= dt.computeCardinality( t, processing );
    }else{
      c *= tc.getCardinality();
    }
  }
  return c;
}

bool DatatypeConstructor::computeWellFounded(
    std::vector<Type>& processing) const
{
  for(const_iterator i = begin(), i_end = end(); i != i_end; ++i) {
    Type t = SelectorType((*i).getSelector().getType()).getRangeType();
    if( t.isDatatype() ){
      const Datatype& dt = ((DatatypeType)t).getDatatype();
      if( !dt.computeWellFounded( processing ) ){
        return false;
      }
    }
  }
  return true;
}

bool DatatypeConstructor::isFinite(Type t) const
{
  PrettyCheckArgument(isResolved(), this, "this datatype constructor is not yet resolved");

  // we're using some internals, so we have to set up this library context
  ExprManagerScope ems(d_constructor);
  TNode self = Node::fromExpr(d_constructor);
  // is this already in the cache ?
  if(self.getAttribute(DatatypeFiniteComputedAttr())) {
    return self.getAttribute(DatatypeFiniteAttr());
  }
  std::vector< Type > instTypes;
  std::vector< Type > paramTypes;
  if( DatatypeType(t).isParametric() ){
    paramTypes = DatatypeType(t).getDatatype().getParameters();
    instTypes = DatatypeType(t).getParamTypes();
  }  
  for(const_iterator i = begin(), i_end = end(); i != i_end; ++i) {
    Type tc = (*i).getRangeType();
    if( DatatypeType(t).isParametric() ){
      tc = tc.substitute( paramTypes, instTypes );
    }
    if(! tc.getCardinality().isFinite()) {
      self.setAttribute(DatatypeFiniteComputedAttr(), true);
      self.setAttribute(DatatypeFiniteAttr(), false);
      return false;
    }
  }
  self.setAttribute(DatatypeFiniteComputedAttr(), true);
  self.setAttribute(DatatypeFiniteAttr(), true);
  return true;
}

bool DatatypeConstructor::isInterpretedFinite(Type t) const
{
  PrettyCheckArgument(isResolved(), this, "this datatype constructor is not yet resolved");
  // we're using some internals, so we have to set up this library context
  ExprManagerScope ems(d_constructor);
  TNode self = Node::fromExpr(d_constructor);
  // is this already in the cache ?
  if(self.getAttribute(DatatypeUFiniteComputedAttr())) {
    return self.getAttribute(DatatypeUFiniteAttr());
  }
  std::vector< Type > instTypes;
  std::vector< Type > paramTypes;
  if( DatatypeType(t).isParametric() ){
    paramTypes = DatatypeType(t).getDatatype().getParameters();
    instTypes = DatatypeType(t).getParamTypes();
  }  
  for(const_iterator i = begin(), i_end = end(); i != i_end; ++i) {
    Type tc = (*i).getRangeType();
    if( DatatypeType(t).isParametric() ){
      tc = tc.substitute( paramTypes, instTypes );
    }
    TypeNode tcn = TypeNode::fromType( tc );
    if(!tcn.isInterpretedFinite()) {
      self.setAttribute(DatatypeUFiniteComputedAttr(), true);
      self.setAttribute(DatatypeUFiniteAttr(), false);
      return false;
    }
  }
  self.setAttribute(DatatypeUFiniteComputedAttr(), true);
  self.setAttribute(DatatypeUFiniteAttr(), true);
  return true;
}

Expr DatatypeConstructor::computeGroundTerm(Type t,
                                            std::vector<Type>& processing,
                                            std::map<Type, Expr>& gt) const
{
  // we're using some internals, so we have to set up this library context
  ExprManagerScope ems(d_constructor);

  std::vector<Expr> groundTerms;
  groundTerms.push_back(getConstructor());

  // for each selector, get a ground term
  std::vector< Type > instTypes;
  std::vector< Type > paramTypes;
  if( DatatypeType(t).isParametric() ){
    paramTypes = DatatypeType(t).getDatatype().getParameters();
    instTypes = DatatypeType(t).getParamTypes();
  }
  for(const_iterator i = begin(), i_end = end(); i != i_end; ++i) {
    Type selType = SelectorType((*i).getSelector().getType()).getRangeType();
    if( DatatypeType(t).isParametric() ){
      selType = selType.substitute( paramTypes, instTypes );
    }
    Expr arg;
    if( selType.isDatatype() ){
      std::map< Type, Expr >::iterator itgt = gt.find( selType );
      if( itgt != gt.end() ){
        arg = itgt->second;
      }else{
        const Datatype & dt = DatatypeType(selType).getDatatype();
        arg = dt.computeGroundTerm( selType, processing );
      }
    }else{
      arg = selType.mkGroundTerm();
    }
    if( arg.isNull() ){
      Debug("datatypes") << "...unable to construct arg of " << (*i).getName() << std::endl;
      return Expr();
    }else{
      Debug("datatypes") << "...constructed arg " << arg.getType() << std::endl;
      groundTerms.push_back(arg);
    }
  }

  Expr groundTerm = getConstructor().getExprManager()->mkExpr(kind::APPLY_CONSTRUCTOR, groundTerms);
  if( groundTerm.getType()!=t ){
    Assert( Datatype::datatypeOf( d_constructor ).isParametric() );
    //type is ambiguous, must apply type ascription
    Debug("datatypes-gt") << "ambiguous type for " << groundTerm << ", ascribe to " << t << std::endl;
    groundTerms[0] = getConstructor().getExprManager()->mkExpr(kind::APPLY_TYPE_ASCRIPTION,
                       getConstructor().getExprManager()->mkConst(AscriptionType(getSpecializedConstructorType(t))),
                       groundTerms[0]);
    groundTerm = getConstructor().getExprManager()->mkExpr(kind::APPLY_CONSTRUCTOR, groundTerms);
  }
  return groundTerm;
}

void DatatypeConstructor::computeSharedSelectors( Type domainType ) const {
  if( d_shared_selectors[domainType].size()<getNumArgs() ){
    TypeNode ctype;
    if( DatatypeType(domainType).isParametric() ){
      ctype = TypeNode::fromType( getSpecializedConstructorType( domainType ) );
    }else{
      ctype = TypeNode::fromType( d_constructor.getType() );
    }
    Assert( ctype.isConstructor() );
    Assert( ctype.getNumChildren()-1==getNumArgs() );
    //compute the shared selectors
    const Datatype& dt = Datatype::datatypeOf(d_constructor);
    std::map< TypeNode, unsigned > counter;
    for( unsigned j=0; j<ctype.getNumChildren()-1; j++ ){
      TypeNode t = ctype[j];
      Expr ss = dt.getSharedSelector( domainType, t.toType(), counter[t] );
      d_shared_selectors[domainType].push_back( ss );
      Assert( d_shared_selector_index[domainType].find( ss )==d_shared_selector_index[domainType].end() );
      d_shared_selector_index[domainType][ss] = j;
      counter[t]++;
    }
  }
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
  IllegalArgument(name, "No such arg `%s' of constructor `%s'", name.c_str(), d_name.c_str());
}

Expr DatatypeConstructor::getSelector(std::string name) const {
  return (*this)[name].getSelector();
}

Type DatatypeConstructor::getArgType(unsigned index) const
{
  PrettyCheckArgument(index < getNumArgs(), index, "index out of bounds");
  return static_cast<SelectorType>((*this)[index].getType()).getRangeType();
}

bool DatatypeConstructor::involvesExternalType() const{
  for(const_iterator i = begin(); i != end(); ++i) {
    if(! SelectorType((*i).getSelector().getType()).getRangeType().isDatatype()) {
      return true;
    }
  }
  return false;
}

bool DatatypeConstructor::involvesUninterpretedType() const{
  for(const_iterator i = begin(); i != end(); ++i) {
    if(SelectorType((*i).getSelector().getType()).getRangeType().isSort()) {
      return true;
    }
  }
  return false;
}

DatatypeConstructorArg::DatatypeConstructorArg(std::string name, Expr selector) :
  d_name(name),
  d_selector(selector),
  d_resolved(false) {
  PrettyCheckArgument(name != "", name, "cannot construct a datatype constructor arg without a name");
}

std::string DatatypeConstructorArg::getName() const
{
  string name = d_name;
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
  if( options::dtSharedSelectors() ){
    computeSharedSelectors( domainType );
    Assert( d_shared_selectors[domainType].size()==getNumArgs() );
    return d_shared_selectors[domainType][index];
  }else{
    return d_args[index].getSelector();
  }
}

int DatatypeConstructor::getSelectorIndexInternal( Expr sel ) const {
  PrettyCheckArgument(isResolved(), this, "cannot get an internal selector index for an unresolved datatype constructor");
  if( options::dtSharedSelectors() ){
    Assert( sel.getType().isSelector() );
    Type domainType = ((SelectorType)sel.getType()).getDomain();
    computeSharedSelectors( domainType );
    std::map< Expr, unsigned >::iterator its = d_shared_selector_index[domainType].find( sel );
    if( its!=d_shared_selector_index[domainType].end() ){
      return (int)its->second;
    }
  }else{
    unsigned sindex = Datatype::indexOf(sel);
    if( getNumArgs() > sindex && d_args[sindex].getSelector() == sel ){
      return (int)sindex;
    }
  }
  return -1;
}

Expr DatatypeConstructorArg::getConstructor() const {
  PrettyCheckArgument(isResolved(), this,
                "cannot get a associated constructor for argument of an unresolved datatype constructor");
  return d_constructor;
}

SelectorType DatatypeConstructorArg::getType() const {
  return getSelector().getType();
}

Type DatatypeConstructorArg::getRangeType() const {
  return getType().getRangeType();
}

bool DatatypeConstructorArg::isUnresolvedSelf() const
{
  return d_selector.isNull() && d_name.size() == d_name.find('\0') + 1;
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
  out << getName() << ": ";

  Type t;
  if (isResolved())
  {
    t = getRangeType();
  }
  else if (d_selector.isNull())
  {
    string typeName = d_name.substr(d_name.find('\0') + 1);
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

}/* CVC4 namespace */
