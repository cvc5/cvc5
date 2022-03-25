/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Morgan Deters, Tim King
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Reference-counted encapsulation of a pointer to node information.
 */
#include "expr/type_node.h"

#include <vector>

#include "expr/datatype_index.h"
#include "expr/dtype_cons.h"
#include "expr/node_manager_attributes.h"
#include "expr/type_properties.h"
#include "options/base_options.h"
#include "options/quantifiers_options.h"
#include "theory/type_enumerator.h"
#include "util/bitvector.h"
#include "util/cardinality.h"

using namespace std;

namespace cvc5 {

TypeNode TypeNode::s_null( &expr::NodeValue::null() );

TypeNode TypeNode::substitute(
    const TypeNode& type,
    const TypeNode& replacement,
    std::unordered_map<TypeNode, TypeNode>& cache) const
{
  // in cache?
  std::unordered_map<TypeNode, TypeNode>::const_iterator i = cache.find(*this);
  if(i != cache.end()) {
    return (*i).second;
  }
  else if (*this == type)
  {
    return replacement;
  }

  if (d_nv->getNumChildren() == 0)
  {
    return *this;
  }

  // otherwise compute
  NodeBuilder nb(getKind());
  if(getMetaKind() == kind::metakind::PARAMETERIZED) {
    // push the operator
    nb << TypeNode(d_nv->d_children[0]);
  }
  for (TypeNode::const_iterator j = begin(), iend = end(); j != iend; ++j)
  {
    if (*j == type)
    {
      nb << replacement;
    }
    else
    {
      nb << (*j).substitute(type, replacement);
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

/** Attribute true for types that have cardinality one */
struct TypeCardinalityClassTag
{
};
typedef expr::Attribute<TypeCardinalityClassTag, uint64_t>
    TypeCardinalityClassAttr;

CardinalityClass TypeNode::getCardinalityClass()
{
  // check it is already cached
  if (hasAttribute(TypeCardinalityClassAttr()))
  {
    return static_cast<CardinalityClass>(
        getAttribute(TypeCardinalityClassAttr()));
  }
  CardinalityClass ret = CardinalityClass::INFINITE;
  if (isSort())
  {
    ret = CardinalityClass::INTERPRETED_ONE;
  }
  else if (isBoolean() || isBitVector() || isFloatingPoint()
           || isRoundingMode())
  {
    ret = CardinalityClass::FINITE;
  }
  else if (isString() || isRegExp() || isSequence() || isRealOrInt() || isBag())
  {
    ret = CardinalityClass::INFINITE;
  }
  else
  {
    // recursive case (this may be a parametric sort), we assume infinite for
    // the moment here to prevent infinite loops, which may occur when
    // computing the cardinality of datatype types with foreign types
    setAttribute(TypeCardinalityClassAttr(), static_cast<uint64_t>(ret));

    if (isDatatype())
    {
      TypeNode tn = *this;
      const DType& dt = getDType();
      ret = dt.getCardinalityClass(tn);
    }
    else if (isArray())
    {
      ret = getArrayConstituentType().getCardinalityClass();
      if (ret == CardinalityClass::FINITE
          || ret == CardinalityClass::INTERPRETED_FINITE)
      {
        CardinalityClass cci = getArrayIndexType().getCardinalityClass();
        // arrays with both finite element types, we take the max with its
        // index type.
        ret = maxCardinalityClass(ret, cci);
      }
      // else, array types whose element type is INFINITE, ONE, or
      // INTERPRETED_ONE have the same cardinality class as their range.
    }
    else if (isSet())
    {
      CardinalityClass cc = getSetElementType().getCardinalityClass();
      if (cc == CardinalityClass::ONE)
      {
        // 1 -> 2
        ret = CardinalityClass::FINITE;
      }
      else if (ret == CardinalityClass::INTERPRETED_ONE)
      {
        // maybe 1 -> maybe finite
        ret = CardinalityClass::INTERPRETED_FINITE;
      }
      else
      {
        // finite or infinite is unchanged
        ret = cc;
      }
    }
    else if (isFunction())
    {
      ret = getRangeType().getCardinalityClass();
      if (ret == CardinalityClass::FINITE
          || ret == CardinalityClass::INTERPRETED_FINITE)
      {
        // we may have a larger cardinality class based on the
        // arguments of the function
        std::vector<TypeNode> argTypes = getArgTypes();
        for (size_t i = 0, nargs = argTypes.size(); i < nargs; i++)
        {
          CardinalityClass cca = argTypes[i].getCardinalityClass();
          ret = maxCardinalityClass(ret, cca);
        }
      }
      // else, function types whose range type is INFINITE, ONE, or
      // INTERPRETED_ONE have the same cardinality class as their range.
    }
    else if (isConstructor())
    {
      // notice that we require computing the cardinality class of the
      // constructor type, which is equivalent to asking how many
      // constructor applications of the given constructor exist. This
      // is used in several places in the decision procedure for datatypes.
      // The cardinality starts with one.
      ret = CardinalityClass::ONE;
      // we may have a larger cardinality class based on the
      // arguments of the constructor
      std::vector<TypeNode> argTypes = getArgTypes();
      for (size_t i = 0, nargs = argTypes.size(); i < nargs; i++)
      {
        CardinalityClass cca = argTypes[i].getCardinalityClass();
        ret = maxCardinalityClass(ret, cca);
      }
    }
    else
    {
      // all types we care about should be handled above
      Assert(false);
    }
  }
  setAttribute(TypeCardinalityClassAttr(), static_cast<uint64_t>(ret));
  return ret;
}

/** Attribute true for types that are closed enumerable */
struct IsClosedEnumerableTag
{
};
struct IsClosedEnumerableComputedTag
{
};
typedef expr::Attribute<IsClosedEnumerableTag, bool> IsClosedEnumerableAttr;
typedef expr::Attribute<IsClosedEnumerableComputedTag, bool>
    IsClosedEnumerableComputedAttr;

bool TypeNode::isClosedEnumerable()
{
  // check it is already cached
  if (!getAttribute(IsClosedEnumerableComputedAttr()))
  {
    bool ret = true;
    if (isArray() || isSort() || isCodatatype() || isFunction() || isRegExp())
    {
      ret = false;
    }
    else if (isSet())
    {
      ret = getSetElementType().isClosedEnumerable();
    }
    else if (isSequence())
    {
      ret = getSequenceElementType().isClosedEnumerable();
    }
    else if (isDatatype())
    {
      // avoid infinite loops: initially set to true
      setAttribute(IsClosedEnumerableAttr(), ret);
      setAttribute(IsClosedEnumerableComputedAttr(), true);
      TypeNode tn = *this;
      const DType& dt = getDType();
      for (uint32_t i = 0, ncons = dt.getNumConstructors(); i < ncons; i++)
      {
        for (uint32_t j = 0, nargs = dt[i].getNumArgs(); j < nargs; j++)
        {
          TypeNode ctn = dt[i][j].getRangeType();
          if (tn != ctn && !ctn.isClosedEnumerable())
          {
            ret = false;
            break;
          }
        }
        if (!ret)
        {
          break;
        }
      }
    }
    setAttribute(IsClosedEnumerableAttr(), ret);
    setAttribute(IsClosedEnumerableComputedAttr(), true);
    return ret;
  }
  return getAttribute(IsClosedEnumerableAttr());
}

bool TypeNode::isFirstClass() const
{
  return getKind() != kind::CONSTRUCTOR_TYPE && getKind() != kind::SELECTOR_TYPE
         && getKind() != kind::TESTER_TYPE && getKind() != kind::UPDATER_TYPE
         && (getKind() != kind::TYPE_CONSTANT
             || (getConst<TypeConstant>() != REGEXP_TYPE
                 && getConst<TypeConstant>() != SEXPR_TYPE));
}

bool TypeNode::isWellFounded() const {
  return kind::isWellFounded(*this);
}

bool TypeNode::isStringLike() const { return isString() || isSequence(); }

// !!! Note that this will change to isReal() || isInteger() when subtyping is
// eliminated
bool TypeNode::isRealOrInt() const { return isReal(); }

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
  if (isFunction() && t.isFunction())
  {
    if (!isComparableTo(t))
    {
      // incomparable, not subtype
      return false;
    }
    return getRangeType().isSubtypeOf(t.getRangeType());
  }
  // this should only return true for types T1, T2 where we handle equalities between T1 and T2
  // (more cases go here, if we want to support such cases)
  return false;
}

bool TypeNode::isComparableTo(TypeNode t) const {
  if(*this == t) {
    return true;
  }
  if(isSubtypeOf(NodeManager::currentNM()->realType())) {
    return t.isSubtypeOf(NodeManager::currentNM()->realType());
  }
  if (isFunction() && t.isFunction())
  {
    // comparable if they have a common type node
    return !leastCommonTypeNode(*this, t).isNull();
  }
  return false;
}

TypeNode TypeNode::getTesterDomainType() const
{
  Assert(isTester());
  return (*this)[0];
}

TypeNode TypeNode::getSequenceElementType() const
{
  Assert(isSequence());
  return (*this)[0];
}

TypeNode TypeNode::getBaseType() const {
  TypeNode realt = NodeManager::currentNM()->realType();
  if (isSubtypeOf(realt)) {
    return realt;
  } else if (isParametricDatatype()) {
    std::vector<TypeNode> v;
    for(size_t i = 1; i < getNumChildren(); ++i) {
      v.push_back((*this)[i].getBaseType());
    }
    return (*this)[0].getDType().getTypeNode().instantiateParametricDatatype(v);
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

bool TypeNode::isTuple() const
{
  return (getKind() == kind::DATATYPE_TYPE && getDType().isTuple());
}

bool TypeNode::isRecord() const
{
  return (getKind() == kind::DATATYPE_TYPE && getDType().isRecord());
}

size_t TypeNode::getTupleLength() const {
  Assert(isTuple());
  const DType& dt = getDType();
  Assert(dt.getNumConstructors() == 1);
  return dt[0].getNumArgs();
}

vector<TypeNode> TypeNode::getTupleTypes() const {
  Assert(isTuple());
  const DType& dt = getDType();
  Assert(dt.getNumConstructors() == 1);
  vector<TypeNode> types;
  for(unsigned i = 0; i < dt[0].getNumArgs(); ++i) {
    types.push_back(dt[0][i].getRangeType());
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
  const DType& dt = (*this)[0].getDType();
  unsigned n = dt.getNumParameters();
  Assert(n < getNumChildren());
  for(unsigned i = 0; i < n; ++i) {
    if (dt.getParameter(i) == (*this)[i + 1])
    {
      return false;
    }
  }
  return true;
}

TypeNode TypeNode::instantiateParametricDatatype(
    const std::vector<TypeNode>& params) const
{
  AssertArgument(getKind() == kind::PARAMETRIC_DATATYPE, *this);
  AssertArgument(params.size() == getNumChildren() - 1, *this);
  NodeManager* nm = NodeManager::currentNM();
  TypeNode cons = nm->mkTypeConst((*this)[0].getConst<DatatypeIndexConstant>());
  std::vector<TypeNode> paramsNodes;
  paramsNodes.push_back(cons);
  for (const TypeNode& t : params)
  {
    paramsNodes.push_back(t);
  }
  return nm->mkTypeNode(kind::PARAMETRIC_DATATYPE, paramsNodes);
}

uint64_t TypeNode::getSortConstructorArity() const
{
  Assert(isSortConstructor() && hasAttribute(expr::SortArityAttr()));
  return getAttribute(expr::SortArityAttr());
}

std::string TypeNode::getName() const
{
  Assert(isSort() || isSortConstructor());
  return getAttribute(expr::VarNameAttr());
}

TypeNode TypeNode::instantiateSortConstructor(
    const std::vector<TypeNode>& params) const
{
  Assert(isSortConstructor());
  return NodeManager::currentNM()->mkSort(*this, params);
}

/** Is this an instantiated datatype parameter */
bool TypeNode::isParameterInstantiatedDatatype(unsigned n) const {
  AssertArgument(getKind() == kind::PARAMETRIC_DATATYPE, *this);
  const DType& dt = (*this)[0].getDType();
  AssertArgument(n < dt.getNumParameters(), *this);
  return dt.getParameter(n) != (*this)[n + 1];
}

TypeNode TypeNode::leastCommonTypeNode(TypeNode t0, TypeNode t1){
  return commonTypeNode( t0, t1, true );
}

TypeNode TypeNode::mostCommonTypeNode(TypeNode t0, TypeNode t1){
  return commonTypeNode( t0, t1, false );
}

TypeNode TypeNode::commonTypeNode(TypeNode t0, TypeNode t1, bool isLeast) {
  Assert(!t0.isNull());
  Assert(!t1.isNull());

  if(__builtin_expect( (t0 == t1), true )) {
    return t0;
  }

  // t0 != t1 &&
  if(t0.getKind() == kind::TYPE_CONSTANT) {
    switch(t0.getConst<TypeConstant>()) {
    case INTEGER_TYPE:
      if(t1.isInteger()) {
        // t0 == IntegerType && t1.isInteger()
        return t0; //IntegerType
      } else if(t1.isReal()) {
        // t0 == IntegerType && t1.isReal() && !t1.isInteger()
        return isLeast ? t1 : t0; // RealType
      } else {
        return TypeNode(); // null type
      }
    case REAL_TYPE:
      if(t1.isReal()) {
        return isLeast ? t0 : t1; // RealType
      } else {
        return TypeNode(); // null type
      }
    default:
      return TypeNode(); // null type
    }
  } else if(t1.getKind() == kind::TYPE_CONSTANT) {
    return commonTypeNode(t1, t0, isLeast); // decrease the number of special cases
  }

  // t0 != t1 &&
  // t0.getKind() == kind::TYPE_CONSTANT &&
  // t1.getKind() == kind::TYPE_CONSTANT
  switch(t0.getKind()) {
    case kind::FUNCTION_TYPE:
    {
      if (t1.getKind() != kind::FUNCTION_TYPE)
      {
        return TypeNode();
      }
      // must have equal arguments
      std::vector<TypeNode> t0a = t0.getArgTypes();
      std::vector<TypeNode> t1a = t1.getArgTypes();
      if (t0a.size() != t1a.size())
      {
        // different arities
        return TypeNode();
      }
      for (unsigned i = 0, nargs = t0a.size(); i < nargs; i++)
      {
        if (t0a[i] != t1a[i])
        {
          // an argument is different
          return TypeNode();
        }
      }
      TypeNode t0r = t0.getRangeType();
      TypeNode t1r = t1.getRangeType();
      TypeNode tr = commonTypeNode(t0r, t1r, isLeast);
      std::vector<TypeNode> ftypes;
      ftypes.insert(ftypes.end(), t0a.begin(), t0a.end());
      ftypes.push_back(tr);
      return NodeManager::currentNM()->mkFunctionType(ftypes);
    }
    break;
    case kind::BITVECTOR_TYPE:
    case kind::FLOATINGPOINT_TYPE:
    case kind::SORT_TYPE:
    case kind::CONSTRUCTOR_TYPE:
    case kind::SELECTOR_TYPE:
    case kind::TESTER_TYPE:
    case kind::ARRAY_TYPE:
    case kind::DATATYPE_TYPE:
    case kind::PARAMETRIC_DATATYPE:
    case kind::SEQUENCE_TYPE:
    case kind::SET_TYPE:
    case kind::BAG_TYPE:
    {
      // we don't support subtyping except for built in types Int and Real.
      return TypeNode();  // return null type
    }
    default:
      Unimplemented() << "don't have a commonType for types `" << t0
                      << "' and `" << t1 << "'";
  }
}

/** Is this a sort kind */
bool TypeNode::isSort() const {
  return ( getKind() == kind::SORT_TYPE && !hasAttribute(expr::SortArityAttr()) );
}

/** Is this a sort constructor kind */
bool TypeNode::isSortConstructor() const {
  return getKind() == kind::SORT_TYPE && hasAttribute(expr::SortArityAttr());
}

bool TypeNode::isFloatingPoint() const
{
  return getKind() == kind::FLOATINGPOINT_TYPE;
}

bool TypeNode::isBitVector() const { return getKind() == kind::BITVECTOR_TYPE; }

bool TypeNode::isDatatype() const
{
  return getKind() == kind::DATATYPE_TYPE
         || getKind() == kind::PARAMETRIC_DATATYPE;
}

bool TypeNode::isParametricDatatype() const
{
  return getKind() == kind::PARAMETRIC_DATATYPE;
}

bool TypeNode::isConstructor() const
{
  return getKind() == kind::CONSTRUCTOR_TYPE;
}

bool TypeNode::isSelector() const { return getKind() == kind::SELECTOR_TYPE; }

bool TypeNode::isTester() const { return getKind() == kind::TESTER_TYPE; }

bool TypeNode::isUpdater() const { return getKind() == kind::UPDATER_TYPE; }

bool TypeNode::isCodatatype() const
{
  if (isDatatype())
  {
    return getDType().isCodatatype();
  }
  return false;
}

bool TypeNode::isSygusDatatype() const
{
  if (isDatatype())
  {
    return getDType().isSygus();
  }
  return false;
}

std::string TypeNode::toString() const {
  std::stringstream ss;
  d_nv->toStream(ss, -1, 0);
  return ss.str();
}

const DType& TypeNode::getDType() const
{
  if (getKind() == kind::DATATYPE_TYPE)
  {
    DatatypeIndexConstant dic = getConst<DatatypeIndexConstant>();
    return NodeManager::currentNM()->getDTypeForIndex(dic.getIndex());
  }
  Assert(getKind() == kind::PARAMETRIC_DATATYPE);
  return (*this)[0].getDType();
}

bool TypeNode::isBag() const
{
  return getKind() == kind::BAG_TYPE;
}

TypeNode TypeNode::getBagElementType() const
{
  Assert(isBag());
  return (*this)[0];
}

bool TypeNode::isBitVector(unsigned size) const
{
  return (getKind() == kind::BITVECTOR_TYPE
          && getConst<BitVectorSize>() == size);
}

uint32_t TypeNode::getBitVectorSize() const
{
  Assert(isBitVector());
  return getConst<BitVectorSize>();
}

TypeNode TypeNode::getRangeType() const
{
  if (isTester())
  {
    return NodeManager::currentNM()->booleanType();
  }
  Assert(isFunction() || isConstructor() || isSelector())
      << "Cannot get range type of " << *this;
  return (*this)[getNumChildren() - 1];
}

}  // namespace cvc5

namespace std {

size_t hash<cvc5::TypeNode>::operator()(const cvc5::TypeNode& tn) const
{
  return tn.getId();
}

}  // namespace std
