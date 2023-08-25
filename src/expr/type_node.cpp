/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Aina Niemetz, Morgan Deters
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Reference-counted encapsulation of a pointer to node information.
 */
#include "expr/type_node.h"

#include <cmath>
#include <vector>

#include "expr/dtype_cons.h"
#include "expr/node_manager_attributes.h"
#include "expr/type_properties.h"
#include "options/base_options.h"
#include "options/quantifiers_options.h"
#include "theory/builtin/abstract_type.h"
#include "theory/fp/theory_fp_utils.h"
#include "theory/type_enumerator.h"
#include "util/bitvector.h"
#include "util/cardinality.h"
#include "util/finite_field_value.h"
#include "util/integer.h"

using namespace std;

namespace cvc5::internal {

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
  if (isUninterpretedSort())
  {
    ret = CardinalityClass::INTERPRETED_ONE;
  }
  else if (isBoolean() || isBitVector() || isFloatingPoint() || isRoundingMode()
           || isFiniteField())
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
    else if (isDatatypeConstructor())
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

bool TypeNode::isCardinalityLessThan(size_t n)
{
  if (isBoolean())
  {
    return n > 2;
  }
  if (isBitVector())
  {
    return std::log2(n) > getBitVectorSize();
  }
  if (isFloatingPoint())
  {
    return Integer(n) > theory::fp::utils::getCardinality(*this);
  }
  if (isRoundingMode())
  {
    return n > 5;
  }
  if (isFiniteField())
  {
    return Integer(n) > getFfSize();
  }
  return false;
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
    if (isArray() || isUninterpretedSort() || isCodatatype() || isFunction()
        || isRegExp())
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
  Kind k = getKind();
  return k != kind::CONSTRUCTOR_TYPE && k != kind::SELECTOR_TYPE
         && k != kind::TESTER_TYPE && k != kind::UPDATER_TYPE
         && k != kind::ABSTRACT_TYPE
         && (k != kind::TYPE_CONSTANT
             || (getConst<TypeConstant>() != REGEXP_TYPE
                 && getConst<TypeConstant>() != SEXPR_TYPE));
}

bool TypeNode::isWellFounded() const {
  return kind::isWellFounded(*this);
}

bool TypeNode::isInteger() const
{
  return getKind() == kind::TYPE_CONSTANT
         && getConst<TypeConstant>() == INTEGER_TYPE;
}

bool TypeNode::isReal() const
{
  return getKind() == kind::TYPE_CONSTANT
         && getConst<TypeConstant>() == REAL_TYPE;
}

bool TypeNode::isStringLike() const { return isString() || isSequence(); }

bool TypeNode::isInstanceOf(const TypeNode& t) const
{
  return leastUpperBound(t) == (*this);
}

TypeNode TypeNode::leastUpperBound(const TypeNode& t) const
{
  return unifyInternal(t, true);
}

TypeNode TypeNode::greatestLowerBound(const TypeNode& t) const
{
  return unifyInternal(t, false);
}

TypeNode TypeNode::unifyInternal(const TypeNode& t, bool isLub) const
{
  Assert(!isNull() && !t.isNull());
  if (*this == t)
  {
    return t;
  }
  if (t.isAbstract())
  {
    Kind tak = t.getAbstractedKind();
    if (tak == kind::ABSTRACT_TYPE)
    {
      // everything is unifiable with the fully abstract type
      return isLub ? *this : t;
    }
    // ABSTRACT_TYPE{k} is unifiable with types with kind k
    if (getKind() == tak)
    {
      return isLub ? *this : t;
    }
  }
  // same as above, swapping this and t
  if (isAbstract())
  {
    Kind ak = getAbstractedKind();
    if (ak == kind::ABSTRACT_TYPE)
    {
      return isLub ? t : *this;
    }
    if (t.getKind() == ak)
    {
      return isLub ? t : *this;
    }
  }
  Kind k = getKind();
  if (k == kind::TYPE_CONSTANT || k != t.getKind())
  {
    // different kinds, or distinct constants
    return TypeNode::null();
  }
  size_t nchild = getNumChildren();
  if (nchild == 0 || nchild != t.getNumChildren())
  {
    // different arities
    return TypeNode::null();
  }
  NodeBuilder nb(k);
  for (size_t i = 0; i < nchild; i++)
  {
    TypeNode c = (*this)[i];
    TypeNode tc = t[i];
    TypeNode jc = c.unifyInternal(tc, isLub);
    if (jc.isNull())
    {
      // incompatible component type
      return jc;
    }
    nb << jc;
  }
  return nb.constructTypeNode();
}

bool TypeNode::isComparableTo(const TypeNode& t) const
{
  // could do join or meet here
  return !unifyInternal(t, true).isNull();
}

bool TypeNode::isRealOrInt() const { return isReal() || isInteger(); }

TypeNode TypeNode::getDatatypeTesterDomainType() const
{
  Assert(isDatatypeTester());
  return (*this)[0];
}

TypeNode TypeNode::getSequenceElementType() const
{
  Assert(isSequence());
  return (*this)[0];
}

std::vector<TypeNode> TypeNode::getArgTypes() const {
  vector<TypeNode> args;
  if (isDatatypeTester())
  {
    Assert(getNumChildren() == 1);
    args.push_back((*this)[0]);
  }
  else
  {
    Assert(isFunction() || isDatatypeConstructor() || isDatatypeSelector()
           || isDatatypeUpdater());
    for (uint32_t i = 0, i_end = getNumChildren() - 1; i < i_end; ++i)
    {
      args.push_back((*this)[i]);
    }
  }
  return args;
}

std::vector<TypeNode> TypeNode::getInstantiatedParamTypes() const
{
  Assert(isInstantiated());
  vector<TypeNode> params;
  for (uint32_t i = 1, i_end = getNumChildren(); i < i_end; ++i)
  {
    params.push_back((*this)[i]);
  }
  return params;
}

bool TypeNode::isTuple() const { return getKind() == kind::TUPLE_TYPE; }

bool TypeNode::isRecord() const
{
  return (getKind() == kind::DATATYPE_TYPE && getDType().isRecord());
}

size_t TypeNode::getTupleLength() const {
  Assert(isTuple());
  return getNumChildren();
}

vector<TypeNode> TypeNode::getTupleTypes() const {
  Assert(isTuple());
  std::vector<TypeNode> args;
  for (uint32_t i = 0, i_end = getNumChildren(); i < i_end; ++i)
  {
    args.push_back((*this)[i]);
  }
  return args;
}

/** Is this an instantiated datatype type */
bool TypeNode::isInstantiatedDatatype() const {
  Kind k = getKind();
  if (k == kind::DATATYPE_TYPE || k == kind::TUPLE_TYPE)
  {
    return true;
  }
  if (k != kind::PARAMETRIC_DATATYPE)
  {
    return false;
  }
  const DType& dt = (*this)[0].getDType();
  size_t n = dt.getNumParameters();
  Assert(n < getNumChildren());
  for (size_t i = 0; i < n; ++i)
  {
    if (dt.getParameter(i) == (*this)[i + 1])
    {
      return false;
    }
  }
  return true;
}

bool TypeNode::isInstantiatedUninterpretedSort() const
{
  return getKind() == kind::INSTANTIATED_SORT_TYPE;
}

bool TypeNode::isInstantiated() const
{
  return isInstantiatedDatatype() || isInstantiatedUninterpretedSort();
}

TypeNode TypeNode::instantiate(const std::vector<TypeNode>& params) const
{
  NodeManager* nm = NodeManager::currentNM();
  Kind k = getKind();
  TypeNode ret;
  // Note that parametric datatypes we instantiate have an AST where they are
  // applied to their default parameters. In constrast, sort constructors have
  // no children.
  if (k == kind::PARAMETRIC_DATATYPE)
  {
    Assert(params.size() == getNumChildren() - 1);
    TypeNode cons = (*this)[0];
    std::vector<TypeNode> paramsNodes;
    paramsNodes.push_back(cons);
    for (const TypeNode& t : params)
    {
      paramsNodes.push_back(t);
    }
    ret = nm->mkTypeNode(kind::PARAMETRIC_DATATYPE, paramsNodes);
  }
  else
  {
    Assert(isUninterpretedSortConstructor());
    ret = nm->mkSort(*this, params);
  }
  return ret;
}

uint64_t TypeNode::getUninterpretedSortConstructorArity() const
{
  Assert(isUninterpretedSortConstructor()
         && hasAttribute(expr::SortArityAttr()));
  return getAttribute(expr::SortArityAttr());
}

bool TypeNode::isUnresolvedDatatype() const
{
  return getAttribute(expr::UnresolvedDatatypeAttr());
}

bool TypeNode::hasName() const
{
  return hasAttribute(expr::VarNameAttr());
}

std::string TypeNode::getName() const
{
  return getAttribute(expr::VarNameAttr());
}

TypeNode TypeNode::getUninterpretedSortConstructor() const
{
  Assert(getKind() == kind::INSTANTIATED_SORT_TYPE);
  return (*this)[0];
}

bool TypeNode::isParameterInstantiatedDatatype(size_t n) const
{
  Assert(getKind() == kind::PARAMETRIC_DATATYPE);
  const DType& dt = (*this)[0].getDType();
  Assert(n < dt.getNumParameters());
  return dt.getParameter(n) != (*this)[n + 1];
}

/** Is this a sort kind */
bool TypeNode::isUninterpretedSort() const
{
  Kind k = getKind();
  return k == kind::INSTANTIATED_SORT_TYPE
         || (k == kind::SORT_TYPE && !hasAttribute(expr::SortArityAttr()));
}

/** Is this a sort constructor kind */
bool TypeNode::isUninterpretedSortConstructor() const
{
  return getKind() == kind::SORT_TYPE && hasAttribute(expr::SortArityAttr());
}

bool TypeNode::isFloatingPoint() const
{
  return getKind() == kind::FLOATINGPOINT_TYPE;
}

bool TypeNode::isFloatingPoint(unsigned exp, unsigned sig) const
{
  return (getKind() == kind::FLOATINGPOINT_TYPE
          && getConst<FloatingPointSize>().exponentWidth() == exp
          && getConst<FloatingPointSize>().significandWidth() == sig);
}

bool TypeNode::isBitVector() const { return getKind() == kind::BITVECTOR_TYPE; }

bool TypeNode::isDatatype() const
{
  Kind k = getKind();
  return k == kind::DATATYPE_TYPE || k == kind::PARAMETRIC_DATATYPE
         || k == kind::TUPLE_TYPE;
}

bool TypeNode::isParametricDatatype() const
{
  return getKind() == kind::PARAMETRIC_DATATYPE;
}

bool TypeNode::isDatatypeConstructor() const
{
  return getKind() == kind::CONSTRUCTOR_TYPE;
}

bool TypeNode::isDatatypeSelector() const
{
  return getKind() == kind::SELECTOR_TYPE;
}

bool TypeNode::isDatatypeTester() const
{
  return getKind() == kind::TESTER_TYPE;
}

bool TypeNode::isDatatypeUpdater() const
{
  return getKind() == kind::UPDATER_TYPE;
}

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

bool TypeNode::isAbstract() const { return getKind() == kind::ABSTRACT_TYPE; }

bool TypeNode::isFullyAbstract() const
{
  return getKind() == kind::ABSTRACT_TYPE
         && getAbstractedKind() == kind::ABSTRACT_TYPE;
}

Kind TypeNode::getAbstractedKind() const
{
  Assert(isAbstract());
  const AbstractType& ak = getConst<AbstractType>();
  return ak.getKind();
}

bool TypeNode::isMaybeKind(Kind k) const
{
  Kind tk = getKind();
  if (tk == k)
  {
    return true;
  }
  if (tk == kind::ABSTRACT_TYPE)
  {
    Kind tak = getAbstractedKind();
    return tak == kind::ABSTRACT_TYPE || tak == k;
  }
  return false;
}

std::string TypeNode::toString() const {
  std::stringstream ss;
  toStream(ss);
  return ss.str();
}

const DType& TypeNode::getDType() const
{
  return NodeManager::currentNM()->getDTypeFor(*this);
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

unsigned TypeNode::getFloatingPointExponentSize() const
{
  Assert(isFloatingPoint());
  return getConst<FloatingPointSize>().exponentWidth();
}

unsigned TypeNode::getFloatingPointSignificandSize() const
{
  Assert(isFloatingPoint());
  return getConst<FloatingPointSize>().significandWidth();
}

uint32_t TypeNode::getBitVectorSize() const
{
  Assert(isBitVector());
  return getConst<BitVectorSize>();
}

const Integer& TypeNode::getFfSize() const
{
  Assert(getKind() == kind::FINITE_FIELD_TYPE);
  return getConst<FfSize>();
}

TypeNode TypeNode::getRangeType() const
{
  if (isDatatypeTester())
  {
    return NodeManager::currentNM()->booleanType();
  }
  Assert(isFunction() || isDatatypeConstructor() || isDatatypeSelector()
         || isDatatypeUpdater())
      << "Cannot get range type of " << *this;
  return (*this)[getNumChildren() - 1];
}

}  // namespace cvc5::internal

namespace std {

size_t hash<cvc5::internal::TypeNode>::operator()(const cvc5::internal::TypeNode& tn) const
{
  return tn.getId();
}

}  // namespace std
