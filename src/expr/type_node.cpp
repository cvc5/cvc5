/*********************                                                        */
/*! \file type_node.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Morgan Deters, Tim King
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Reference-counted encapsulation of a pointer to node information.
 **
 ** Reference-counted encapsulation of a pointer to node information.
 **/
#include "expr/type_node.h"

#include <vector>

#include "expr/node_manager_attributes.h"
#include "expr/type_properties.h"
#include "options/base_options.h"
#include "options/expr_options.h"
#include "options/quantifiers_options.h"
#include "options/uf_options.h"
#include "theory/type_enumerator.h"

using namespace std;

namespace CVC4 {

TypeNode TypeNode::s_null( &expr::NodeValue::null() );

TypeNode TypeNode::substitute(const TypeNode& type,
                              const TypeNode& replacement,
                              std::unordered_map<TypeNode, TypeNode, HashFunction>& cache) const {
  // in cache?
  std::unordered_map<TypeNode, TypeNode, HashFunction>::const_iterator i = cache.find(*this);
  if(i != cache.end()) {
    return (*i).second;
  }

  // otherwise compute
  NodeBuilder<> nb(getKind());
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
      (*j).substitute(type, replacement);
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

/** Attribute true for types that are finite */
struct IsFiniteTag
{
};
typedef expr::Attribute<IsFiniteTag, bool> IsFiniteAttr;
/** Attribute true for types which we have computed the above attribute */
struct IsFiniteComputedTag
{
};
typedef expr::Attribute<IsFiniteComputedTag, bool> IsFiniteComputedAttr;

/** Attribute true for types that are interpreted as finite */
struct IsInterpretedFiniteTag
{
};
typedef expr::Attribute<IsInterpretedFiniteTag, bool> IsInterpretedFiniteAttr;
/** Attribute true for types which we have computed the above attribute */
struct IsInterpretedFiniteComputedTag
{
};
typedef expr::Attribute<IsInterpretedFiniteComputedTag, bool>
    IsInterpretedFiniteComputedAttr;

bool TypeNode::isFinite() { return isFiniteInternal(false); }

bool TypeNode::isInterpretedFinite()
{
  return isFiniteInternal(options::finiteModelFind());
}

bool TypeNode::isFiniteInternal(bool usortFinite)
{
  // check it is already cached
  if (usortFinite)
  {
    if (getAttribute(IsInterpretedFiniteComputedAttr()))
    {
      return getAttribute(IsInterpretedFiniteAttr());
    }
  }
  else if (getAttribute(IsFiniteComputedAttr()))
  {
    return getAttribute(IsFiniteAttr());
  }
  bool ret = false;
  if (isSort())
  {
    ret = usortFinite;
  }
  else if (isBoolean() || isBitVector() || isFloatingPoint()
           || isRoundingMode())
  {
    ret = true;
  }
  else if (isString() || isRegExp() || isSequence() || isReal())
  {
    ret = false;
  }
  else
  {
    // recursive case (this may be a parametric sort), we assume infinite for
    // the moment here to prevent infinite loops
    if (usortFinite)
    {
      setAttribute(IsInterpretedFiniteAttr(), false);
      setAttribute(IsInterpretedFiniteComputedAttr(), true);
    }
    else
    {
      setAttribute(IsFiniteAttr(), false);
      setAttribute(IsFiniteComputedAttr(), true);
    }
    if (isDatatype())
    {
      TypeNode tn = *this;
      const DType& dt = getDType();
      ret = usortFinite ? dt.isInterpretedFinite(tn) : dt.isFinite(tn);
    }
    else if (isArray())
    {
      TypeNode tnc = getArrayConstituentType();
      if (!tnc.isFiniteInternal(usortFinite))
      {
        // arrays with consistuent type that is infinite are infinite
        ret = false;
      }
      else if (getArrayIndexType().isFiniteInternal(usortFinite))
      {
        // arrays with both finite consistuent and index types are finite
        ret = true;
      }
      else
      {
        // If the consistuent type of the array has cardinality one, then the
        // array type has cardinality one, independent of the index type.
        ret = tnc.getCardinality().isOne();
      }
    }
    else if (isSet())
    {
      ret = getSetElementType().isFiniteInternal(usortFinite);
    }
    else if (isFunction())
    {
      ret = true;
      TypeNode tnr = getRangeType();
      if (!tnr.isFiniteInternal(usortFinite))
      {
        ret = false;
      }
      else
      {
        std::vector<TypeNode> argTypes = getArgTypes();
        for (unsigned i = 0, nargs = argTypes.size(); i < nargs; i++)
        {
          if (!argTypes[i].isFiniteInternal(usortFinite))
          {
            ret = false;
            break;
          }
        }
        if (!ret)
        {
          // similar to arrays, functions are finite if their range type
          // has cardinality one, regardless of the arguments.
          ret = tnr.getCardinality().isOne();
        }
      }
    }
    else
    {
      // all types should be handled above
      Assert(false);
      // by default, compute the exact cardinality for the type and check
      // whether it is finite. This should be avoided in general, since
      // computing cardinalities for types can be highly expensive.
      ret = getCardinality().isFinite();
    }
  }
  if (usortFinite)
  {
    setAttribute(IsInterpretedFiniteAttr(), ret);
    setAttribute(IsInterpretedFiniteComputedAttr(), true);
  }
  else
  {
    setAttribute(IsFiniteAttr(), ret);
    setAttribute(IsFiniteComputedAttr(), true);
  }
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
    if (isArray() || isSort() || isCodatatype() || isFunction())
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
      for (unsigned i = 0, ncons = dt.getNumConstructors(); i < ncons; i++)
      {
        for (unsigned j = 0, nargs = dt[i].getNumArgs(); j < nargs; j++)
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

bool TypeNode::isFirstClass() const {
  return ( getKind() != kind::FUNCTION_TYPE || options::ufHo() ) && 
         getKind() != kind::CONSTRUCTOR_TYPE &&
         getKind() != kind::SELECTOR_TYPE &&
         getKind() != kind::TESTER_TYPE &&
         getKind() != kind::SEXPR_TYPE &&
         ( getKind() != kind::TYPE_CONSTANT ||
           getConst<TypeConstant>() != REGEXP_TYPE );
}

bool TypeNode::isWellFounded() const {
  return kind::isWellFounded(*this);
}

Node TypeNode::mkGroundTerm() const {
  return kind::mkGroundTerm(*this);
}

Node TypeNode::mkGroundValue() const
{
  theory::TypeEnumerator te(*this);
  return *te;
}

bool TypeNode::isStringLike() const { return isString() || isSequence(); }

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
  if(isSet() && t.isSet()) {
    return getSetElementType().isSubtypeOf(t.getSetElementType());
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
  if(isSet() && t.isSet()) {
    return getSetElementType().isComparableTo(t.getSetElementType());
  }
  if (isFunction() && t.isFunction())
  {
    // comparable if they have a common type node
    return !leastCommonTypeNode(*this, t).isNull();
  }
  return false;
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


/** Is this a tuple type? */
bool TypeNode::isTuple() const {
  return (getKind() == kind::DATATYPE_TYPE && getDType().isTuple());
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
  Assert(NodeManager::currentNM() != NULL)
      << "There is no current CVC4::NodeManager associated to this thread.\n"
         "Perhaps a public-facing function is missing a NodeManagerScope ?";

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
    case kind::SEQUENCE_TYPE: return TypeNode();
    case kind::SET_TYPE:
    {
      // take the least common subtype of element types
      TypeNode elementType;
      if (t1.isSet()
          && !(elementType = commonTypeNode(t0[0], t1[0], isLeast)).isNull())
      {
        return NodeManager::currentNM()->mkSetType(elementType);
      }
      else
      {
        return TypeNode();
      }
    }
  case kind::SEXPR_TYPE:
    Unimplemented()
        << "haven't implemented leastCommonType for symbolic expressions yet";
  default:
    Unimplemented() << "don't have a commonType for types `" << t0 << "' and `"
                    << t1 << "'";
  }
}

Node TypeNode::getEnsureTypeCondition( Node n, TypeNode tn ) {
  TypeNode ntn = n.getType();
  Assert(ntn.isComparableTo(tn));
  if( !ntn.isSubtypeOf( tn ) ){
    if( tn.isInteger() ){
      if( tn.isSubtypeOf( ntn ) ){
        return NodeManager::currentNM()->mkNode( kind::IS_INTEGER, n );
      }
    }else if( tn.isDatatype() && ntn.isDatatype() ){
      if( tn.isTuple() && ntn.isTuple() ){
        const DType& dt1 = tn.getDType();
        const DType& dt2 = ntn.getDType();
        NodeManager* nm = NodeManager::currentNM();
        if( dt1[0].getNumArgs()==dt2[0].getNumArgs() ){
          std::vector< Node > conds;
          for( unsigned i=0; i<dt2[0].getNumArgs(); i++ ){
            Node s = nm->mkNode(
                kind::APPLY_SELECTOR_TOTAL, dt2[0][i].getSelector(), n);
            Node etc = getEnsureTypeCondition(s, dt1[0][i].getRangeType());
            if( etc.isNull() ){
              return Node::null();
            }else{
              conds.push_back( etc );
            }
          }
          if( conds.empty() ){
            return nm->mkConst(true);
          }else if( conds.size()==1 ){
            return conds[0];
          }else{
            return nm->mkNode(kind::AND, conds);
          }
        }
      }
    }
    return Node::null();
  }else{
    return NodeManager::currentNM()->mkConst( true );
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

/** Is this a codatatype type */
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
  OutputLanguage outlang = (this == &s_null) ? language::output::LANG_AUTO : options::outputLanguage();
  d_nv->toStream(ss, -1, false, 0, outlang);
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

}/* CVC4 namespace */
