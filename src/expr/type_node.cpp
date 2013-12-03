/*********************                                                        */
/*! \file type_node.cpp
 ** \verbatim
 ** Original author: Dejan Jovanovic
 ** Major contributors: Tim King, Morgan Deters
 ** Minor contributors (to current version): Andrew Reynolds, Clark Barrett
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2013  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief Reference-counted encapsulation of a pointer to node information.
 **
 ** Reference-counted encapsulation of a pointer to node information.
 **/

#include <vector>

#include "expr/node_manager_attributes.h"
#include "expr/type_node.h"
#include "expr/type_properties.h"

using namespace std;

namespace CVC4 {

TypeNode TypeNode::s_null( &expr::NodeValue::s_null );

TypeNode TypeNode::substitute(const TypeNode& type,
                              const TypeNode& replacement,
                              std::hash_map<TypeNode, TypeNode, HashFunction>& cache) const {
  // in cache?
  std::hash_map<TypeNode, TypeNode, HashFunction>::const_iterator i = cache.find(*this);
  if(i != cache.end()) {
    return (*i).second;
  }

  // otherwise compute
  NodeBuilder<> nb(getKind());
  if(getMetaKind() == kind::metakind::PARAMETERIZED) {
    // push the operator
    nb << TypeNode(d_nv->d_children[0]);
  }
  for(TypeNode::const_iterator i = begin(),
        iend = end();
      i != iend;
      ++i) {
    if(*i == type) {
      nb << replacement;
    } else {
      (*i).substitute(type, replacement);
    }
  }

  // put in cache
  TypeNode tn = nb.constructTypeNode();
  cache[*this] = tn;
  return tn;
}

Cardinality TypeNode::getCardinality() const {
  return kind::getCardinality(*this);
}

bool TypeNode::isWellFounded() const {
  return kind::isWellFounded(*this);
}

Node TypeNode::mkGroundTerm() const {
  return kind::mkGroundTerm(*this);
}

bool TypeNode::isSubtypeOf(TypeNode t) const {
  if(*this == t) {
    return true;
  }
  if(getKind() == kind::TYPE_CONSTANT) {
    switch(getConst<TypeConstant>()) {
    case INTEGER_TYPE:
      return t.getKind() == kind::TYPE_CONSTANT && t.getConst<TypeConstant>() == REAL_TYPE;
    default:
      return false;
    }
  }
  if(isSubrange()) {
    if(t.isSubrange()) {
      return t.getSubrangeBounds() <= getSubrangeBounds();
    } else {
      return t.getKind() == kind::TYPE_CONSTANT &&
        ( t.getConst<TypeConstant>() == INTEGER_TYPE ||
          t.getConst<TypeConstant>() == REAL_TYPE );
    }
  }
  if(isTuple() || isRecord()) {
    if(t == NodeManager::currentNM()->getDatatypeForTupleRecord(*this)) {
      return true;
    }
    if(isTuple() != t.isTuple() || isRecord() != t.isRecord()) {
      return false;
    }
    if(isTuple()) {
      if(getNumChildren() != t.getNumChildren()) {
        return false;
      }
      // children must be subtypes of t's, in order
      for(const_iterator i = begin(), j = t.begin(); i != end(); ++i, ++j) {
        if(!(*i).isSubtypeOf(*j)) {
          return false;
        }
      }
    } else {
      const Record& r1 = getConst<Record>();
      const Record& r2 = t.getConst<Record>();
      if(r1.getNumFields() != r2.getNumFields()) {
        return false;
      }
      // r1's fields must be subtypes of r2's, in order
      // names must match also
      for(Record::const_iterator i = r1.begin(), j = r2.begin(); i != r1.end(); ++i, ++j) {
        if((*i).first != (*j).first || !(*i).second.isSubtypeOf((*j).second)) {
          return false;
        }
      }
    }
    return true;
  }
  if(isFunction()) {
    // A function is a subtype of another if the args are the same type, and 
    // the return type is a subtype of the other's.  This is enough for now
    // (and it's necessary for model generation, since a Real-valued function
    // might return a constant Int and thus the model value is typed differently).
    return t.isFunction() &&
           getArgTypes() == t.getArgTypes() &&
           getRangeType().isSubtypeOf(t.getRangeType());
  }
  if(isParametricDatatype() && t.isParametricDatatype()) {
    Assert(getKind() == kind::PARAMETRIC_DATATYPE);
    Assert(t.getKind() == kind::PARAMETRIC_DATATYPE);
    if((*this)[0] != t[0] || getNumChildren() != t.getNumChildren()) {
      return false;
    }
    for(size_t i = 1; i < getNumChildren(); ++i) {
      if(!((*this)[i].isSubtypeOf(t[i]))) {
        return false;
      }
    }
    return true;
  }
  if(isPredicateSubtype()) {
    return getSubtypeParentType().isSubtypeOf(t);
  }
  return false;
}

bool TypeNode::isComparableTo(TypeNode t) const {
  if(*this == t) {
    return true;
  }
  if(isSubtypeOf(NodeManager::currentNM()->realType())) {
    return t.isSubtypeOf(NodeManager::currentNM()->realType());
  }
  if(t.isDatatype() && (isTuple() || isRecord())) {
    if(t.isTuple() || t.isRecord()) {
      if(NodeManager::currentNM()->getDatatypeForTupleRecord(t) ==
         NodeManager::currentNM()->getDatatypeForTupleRecord(*this)) {
        return true;
      }
      if(isTuple() != t.isTuple() || isRecord() != t.isRecord()) {
        return false;
      }
      if(isTuple()) {
        if(getNumChildren() != t.getNumChildren()) {
          return false;
        }
        // children must be comparable to t's, in order
        for(const_iterator i = begin(), j = t.begin(); i != end(); ++i, ++j) {
          if(!(*i).isComparableTo(*j)) {
            return false;
          }
        }
      } else {
        const Record& r1 = getConst<Record>();
        const Record& r2 = t.getConst<Record>();
        if(r1.getNumFields() != r2.getNumFields()) {
          return false;
        }
        // r1's fields must be comparable to r2's, in order
        // names must match also
        for(Record::const_iterator i = r1.begin(), j = r2.begin(); i != r1.end(); ++i, ++j) {
          if((*i).first != (*j).first || !(*i).second.isComparableTo((*j).second)) {
            return false;
          }
        }
      }
      return true;
    } else {
      return t == NodeManager::currentNM()->getDatatypeForTupleRecord(*this);
    }
  } else if(isDatatype() && (t.isTuple() || t.isRecord())) {
    Assert(!isTuple() && !isRecord());// should have been handled above
    return *this == NodeManager::currentNM()->getDatatypeForTupleRecord(t);
  } else if(isParametricDatatype() && t.isParametricDatatype()) {
    Assert(getKind() == kind::PARAMETRIC_DATATYPE);
    Assert(t.getKind() == kind::PARAMETRIC_DATATYPE);
    if((*this)[0] != t[0] || getNumChildren() != t.getNumChildren()) {
      return false;
    }
    for(size_t i = 1; i < getNumChildren(); ++i) {
      if(!((*this)[i].isComparableTo(t[i]))) {
        return false;
      }
    }
    return true;
  }

  if(isPredicateSubtype()) {
    return t.isComparableTo(getSubtypeParentType());
  }
  return false;
}

Node TypeNode::getSubtypePredicate() const {
  Assert(isPredicateSubtype());
  return Node::fromExpr(getConst<Predicate>());
}

TypeNode TypeNode::getSubtypeParentType() const {
  Assert(isPredicateSubtype());
  return getSubtypePredicate().getType().getArgTypes()[0];
}

TypeNode TypeNode::getBaseType() const {
  TypeNode realt = NodeManager::currentNM()->realType();
  if (isSubtypeOf(realt)) {
    return realt;
  } else if (isTuple() || isRecord()) {
    return NodeManager::currentNM()->getDatatypeForTupleRecord(*this);
  } else if (isPredicateSubtype()) {
    return getSubtypeParentType().getBaseType();
  } else if (isParametricDatatype()) {
    vector<Type> v;
    for(size_t i = 1; i < getNumChildren(); ++i) {
      v.push_back((*this)[i].getBaseType().toType());
    }
    TypeNode tn = TypeNode::fromType((*this)[0].getDatatype().getDatatypeType(v));
    return tn;
  }
  return *this;
}

std::vector<TypeNode> TypeNode::getArgTypes() const {
  vector<TypeNode> args;
  if(isTester()) {
    Assert(getNumChildren() == 1);
    args.push_back((*this)[0]);
  } else {
    Assert(isFunction() || isConstructor() || isSelector());
    for(unsigned i = 0, i_end = getNumChildren() - 1; i < i_end; ++i) {
      args.push_back((*this)[i]);
    }
  }
  return args;
}

std::vector<TypeNode> TypeNode::getParamTypes() const {
  vector<TypeNode> params;
  Assert(isParametricDatatype());
  for(unsigned i = 1, i_end = getNumChildren(); i < i_end; ++i) {
    params.push_back((*this)[i]);
  }
  return params;
}

size_t TypeNode::getTupleLength() const {
  Assert(isTuple());
  return getNumChildren();
}

vector<TypeNode> TypeNode::getTupleTypes() const {
  Assert(isTuple());
  vector<TypeNode> types;
  for(unsigned i = 0, i_end = getNumChildren(); i < i_end; ++i) {
    types.push_back((*this)[i]);
  }
  return types;
}

const Record& TypeNode::getRecord() const {
  Assert(isRecord());
  return getConst<Record>();
}

vector<TypeNode> TypeNode::getSExprTypes() const {
  Assert(isSExpr());
  vector<TypeNode> types;
  for(unsigned i = 0, i_end = getNumChildren(); i < i_end; ++i) {
    types.push_back((*this)[i]);
  }
  return types;
}

/** Is this an instantiated datatype type */
bool TypeNode::isInstantiatedDatatype() const {
  if(getKind() == kind::DATATYPE_TYPE) {
    return true;
  }
  if(getKind() != kind::PARAMETRIC_DATATYPE) {
    return false;
  }
  const Datatype& dt = (*this)[0].getConst<Datatype>();
  unsigned n = dt.getNumParameters();
  Assert(n < getNumChildren());
  for(unsigned i = 0; i < n; ++i) {
    if(TypeNode::fromType(dt.getParameter(i)) == (*this)[i + 1]) {
      return false;
    }
  }
  return true;
}

/** Is this an instantiated datatype parameter */
bool TypeNode::isParameterInstantiatedDatatype(unsigned n) const {
  AssertArgument(getKind() == kind::PARAMETRIC_DATATYPE, *this);
  const Datatype& dt = (*this)[0].getConst<Datatype>();
  AssertArgument(n < dt.getNumParameters(), *this);
  return TypeNode::fromType(dt.getParameter(n)) != (*this)[n + 1];
}

TypeNode TypeNode::leastCommonTypeNode(TypeNode t0, TypeNode t1){
  Assert( NodeManager::currentNM() != NULL,
          "There is no current CVC4::NodeManager associated to this thread.\n"
          "Perhaps a public-facing function is missing a NodeManagerScope ?" );

  Assert(!t0.isNull());
  Assert(!t1.isNull());

  if(__builtin_expect( (t0 == t1), true )) {
    return t0;
  } else { // t0 != t1
    if(t0.getKind() == kind::TYPE_CONSTANT) {
      switch(t0.getConst<TypeConstant>()) {
      case INTEGER_TYPE:
        if(t1.isInteger()) {
          // t0 == IntegerType && t1.isInteger()
          return t0; //IntegerType
        } else if(t1.isReal()) {
          // t0 == IntegerType && t1.isReal() && !t1.isInteger()
          return NodeManager::currentNM()->realType(); // RealType
        } else {
          return TypeNode(); // null type
        }
      case REAL_TYPE:
        if(t1.isReal()) {
          return t0; // RealType
        } else {
          return TypeNode(); // null type
        }
      default:
        if(t1.isPredicateSubtype() && t1.getSubtypeParentType().isSubtypeOf(t0)) {
          return t0; // t0 is a constant type
        } else {
          return TypeNode(); // null type
        }
      }
    } else if(t1.getKind() == kind::TYPE_CONSTANT) {
      return leastCommonTypeNode(t1, t0); // decrease the number of special cases
    } else {
      // t0 != t1 &&
      // t0.getKind() == kind::TYPE_CONSTANT &&
      // t1.getKind() == kind::TYPE_CONSTANT
      switch(t0.getKind()) {
      case kind::ARRAY_TYPE:
      case kind::BITVECTOR_TYPE:
      case kind::SORT_TYPE:
      case kind::CONSTRUCTOR_TYPE:
      case kind::SELECTOR_TYPE:
      case kind::TESTER_TYPE:
        if(t1.isPredicateSubtype() && t1.getSubtypeParentType().isSubtypeOf(t0)) {
          return t0;
        } else {
          return TypeNode();
        }
      case kind::FUNCTION_TYPE:
        return TypeNode(); // Not sure if this is right
      case kind::SEXPR_TYPE:
        Unimplemented("haven't implemented leastCommonType for symbolic expressions yet");
        return TypeNode();
      case kind::SUBTYPE_TYPE:
        if(t1.isPredicateSubtype()){
          // This is the case where both t0 and t1 are predicate subtypes.
          return leastCommonPredicateSubtype(t0, t1);
        }else{ // t0 is a predicate subtype and t1 is not
          return leastCommonTypeNode(t1, t0); //decrease the number of special cases
        }
      case kind::SUBRANGE_TYPE:
        if(t1.isSubrange()) {
          const SubrangeBounds& t0SR = t0.getSubrangeBounds();
          const SubrangeBounds& t1SR = t1.getSubrangeBounds();
          if(SubrangeBounds::joinIsBounded(t0SR, t1SR)) {
            SubrangeBounds j = SubrangeBounds::join(t0SR, t1SR);
            return NodeManager::currentNM()->mkSubrangeType(j);
          } else {
            return NodeManager::currentNM()->integerType();
          }
        } else if(t1.isPredicateSubtype()) {
          // t0 is a subrange
          // t1 is not a subrange
          // t1 is a predicate subtype
          if(t1.isInteger()) {
            return NodeManager::currentNM()->integerType();
          } else if(t1.isReal()) {
            return NodeManager::currentNM()->realType();
          } else {
            return TypeNode();
          }
        } else {
          // t0 is a subrange
          // t1 is not a subrange
          // t1 is not a type constant && is not a predicate subtype
          // t1 cannot be real subtype or integer.
          Assert(t1.isReal());
          Assert(t1.isInteger());
          return TypeNode();
        }
      case kind::TUPLE_TYPE: {
        // if the other == this one, we returned already, above
        if(t0.getBaseType() == t1) {
          return t1;
        }
        if(!t1.isTuple() || t0.getNumChildren() != t1.getNumChildren()) {
          // no compatibility between t0, t1
          return TypeNode();
        }
        std::vector<TypeNode> types;
        // construct childwise leastCommonType, if one exists
        for(const_iterator i = t0.begin(), j = t1.begin(); i != t0.end(); ++i, ++j) {
          TypeNode kid = leastCommonTypeNode(*i, *j);
          if(kid.isNull()) {
            // no common supertype: types t0, t1 not compatible
            return TypeNode();
          }
          types.push_back(kid);
        }
        // if we make it here, we constructed the least common type
        return NodeManager::currentNM()->mkTupleType(types);
      }
      case kind::RECORD_TYPE: {
        // if the other == this one, we returned already, above
        if(t0.getBaseType() == t1) {
          return t1;
        }
        const Record& r0 = t0.getConst<Record>();
        if(!t1.isRecord() || r0.getNumFields() != t1.getConst<Record>().getNumFields()) {
          // no compatibility between t0, t1
          return TypeNode();
        }
        std::vector< std::pair<std::string, Type> > fields;
        const Record& r1 = t1.getConst<Record>();
        // construct childwise leastCommonType, if one exists
        for(Record::const_iterator i = r0.begin(), j = r1.begin(); i != r0.end(); ++i, ++j) {
          TypeNode kid = leastCommonTypeNode(TypeNode::fromType((*i).second), TypeNode::fromType((*j).second));
          if((*i).first != (*j).first || kid.isNull()) {
            // if field names differ, or no common supertype, then
            // types t0, t1 not compatible
            return TypeNode();
          }
          fields.push_back(std::make_pair((*i).first, kid.toType()));
        }
        // if we make it here, we constructed the least common type
        return NodeManager::currentNM()->mkRecordType(Record(fields));
      }
      case kind::DATATYPE_TYPE:
        // t1 might be a subtype tuple or record
        if(t1.getBaseType() == t0) {
          return t0;
        }
        // otherwise no common ancestor
        return TypeNode();
      case kind::PARAMETRIC_DATATYPE: {
        if(!t1.isParametricDatatype()) {
          return TypeNode();
        }
        while(t1.getKind() != kind::PARAMETRIC_DATATYPE) {
          t1 = t1.getSubtypeParentType();
        }
        if(t0[0] != t1[0] || t0.getNumChildren() != t1.getNumChildren()) {
          return TypeNode();
        }
        vector<Type> v;
        for(size_t i = 1; i < t0.getNumChildren(); ++i) {
          v.push_back(leastCommonTypeNode(t0[i], t1[i]).toType());
        }
        return TypeNode::fromType(t0[0].getDatatype().getDatatypeType(v));
      }
      default:
        Unimplemented("don't have a leastCommonType for types `%s' and `%s'", t0.toString().c_str(), t1.toString().c_str());
        return TypeNode();
      }
    }
  }
}

TypeNode TypeNode::leastCommonPredicateSubtype(TypeNode t0, TypeNode t1){
  Assert(t0.isPredicateSubtype());
  Assert(t1.isPredicateSubtype());

  std::vector<TypeNode> t0stack;
  t0stack.push_back(t0);
  while(t0stack.back().isPredicateSubtype()){
    t0stack.push_back(t0stack.back().getSubtypeParentType());
  }
  std::vector<TypeNode> t1stack;
  t1stack.push_back(t1);
  while(t1stack.back().isPredicateSubtype()){
    t1stack.push_back(t1stack.back().getSubtypeParentType());
  }

  Assert(!t0stack.empty());
  Assert(!t1stack.empty());

  if(t0stack.back() == t1stack.back()){
    TypeNode mostGeneral = t1stack.back();
    t0stack.pop_back(); t1stack.pop_back();
    while(!t0stack.empty() && t1stack.empty() && t0stack.back() == t1stack.back()){
      mostGeneral = t0stack.back();
      t0stack.pop_back(); t1stack.pop_back();
    }
    return mostGeneral;
  }else{
    return leastCommonTypeNode(t0stack.back(), t1stack.back());
  }
}

/** Is this a sort kind */
bool TypeNode::isSort() const {
  return ( getKind() == kind::SORT_TYPE && !hasAttribute(expr::SortArityAttr()) ) ||
    ( isPredicateSubtype() && getSubtypeParentType().isSort() );
}

/** Is this a sort constructor kind */
bool TypeNode::isSortConstructor() const {
  return getKind() == kind::SORT_TYPE && hasAttribute(expr::SortArityAttr());
}

}/* CVC4 namespace */
