/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Implementation of Alethe node conversion
 */

#include "proof/alethe/alethe_node_converter.h"

#include "expr/dtype.h"
#include "expr/node_algorithm.h"
#include "expr/skolem_manager.h"
#include "proof/proof_rule_checker.h"
#include "theory/builtin/generic_op.h"
#include "util/bitvector.h"
#include "util/rational.h"

namespace cvc5::internal {
namespace proof {

Node AletheNodeConverter::maybeConvert(Node n, bool isAssumption)
{
  d_error = "";
  Node res = convert(n);
  if (!d_error.empty())
  {
    return Node::null();
  }
  if (isAssumption)
  {
    d_convToOriginalAssumption[res] = n;
  }
  return res;
}

void collectTypes(std::vector<TypeNode>& allTypesVec,
                  std::unordered_set<TypeNode>& allTypes)
{
  for (size_t i = 0, size = allTypesVec.size(); i < size; ++i)
  {
    TypeNode tn = allTypesVec[i];
    // Must additionally get the subfield types from datatypes.
    if (tn.isDatatype())
    {
      const DType& dt = tn.getDType();
      std::unordered_set<TypeNode> sftypes = dt.getSubfieldTypes();
      std::unordered_set<TypeNode> sfctypes;
      // get the component types of each of the subfield types
      for (const TypeNode& sft : sftypes)
      {
        // as an optimization, if we've already considered this type, don't
        // have to find its component types
        if (allTypes.find(sft) == allTypes.end())
        {
          expr::getComponentTypes(sft, sfctypes);
        }
      }
      for (const TypeNode& sft : sfctypes)
      {
        if (allTypes.find(sft) == allTypes.end())
        {
          allTypesVec.emplace_back(sft);
          allTypes.insert(sft);
        }
      }
    }
  }
}

Node AletheNodeConverter::recordUnsupportedKind(Kind k)
{
  Trace("alethe-conv") << "AletheNodeConverter: ...unsupported kind\n";
  std::stringstream ss;
  ss << "\"Proof unsupported by Alethe: contains operator " << k << "\"";
  d_error = ss.str();
  return Node::null();
}

Node AletheNodeConverter::postConvert(Node n)
{
  Kind k = n.getKind();
  Trace("alethe-conv") << "AletheNodeConverter: convert " << n << ", kind " << k
                       << "\n";
  switch (k)
  {
    case Kind::BITVECTOR_BIT:
    {
      if (d_isTesting)
      {
        return recordUnsupportedKind(k);
      }
      std::stringstream ss;
      ss << "(_ @bit_of " << n.getOperator().getConst<BitVectorBit>().d_bitIndex
         << ")";
      // Use n0Type to ensure deterministic node ID assignments
      TypeNode n0Type = n[0].getType();
      TypeNode fType = d_nm->mkFunctionType(n0Type, n.getType());
      Node op = mkInternalSymbol(ss.str(), fType, true);
      Node converted = d_nm->mkNode(Kind::APPLY_UF, op, n[0]);
      return converted;
    }
    case Kind::BITVECTOR_FROM_BOOLS:
    {
      if (d_isTesting)
      {
        return recordUnsupportedKind(k);
      }
      std::vector<Node> children;
      std::vector<TypeNode> childrenTypes;
      for (const Node& c : n)
      {
        childrenTypes.push_back(c.getType());
        children.push_back(c);
      }
      TypeNode fType = d_nm->mkFunctionType(childrenTypes, n.getType());
      Node op = mkInternalSymbol("@bbterm", fType, true);
      children.insert(children.begin(), op);
      Node converted = d_nm->mkNode(Kind::APPLY_UF, children);
      return converted;
    }
    case Kind::BITVECTOR_EAGER_ATOM:
    {
      if (d_isTesting)
      {
        return recordUnsupportedKind(k);
      }
      return n[0];
    }
    case Kind::DIVISION_TOTAL:
    {
      return d_nm->mkNode(Kind::DIVISION, n[0], n[1]);
    }
    case Kind::INTS_DIVISION_TOTAL:
    {
      return d_nm->mkNode(Kind::INTS_DIVISION, n[0], n[1]);
    }
    case Kind::INTS_MODULUS_TOTAL:
    {
      return d_nm->mkNode(Kind::INTS_MODULUS, n[0], n[1]);
    }
    case Kind::SKOLEM:
    {
      Trace("alethe-conv") << "AletheNodeConverter: handling skolem " << n
                           << "\n";
      SkolemManager* sm = d_nm->getSkolemManager();
      SkolemId sfi = SkolemId::NONE;
      Node cacheVal;
      sm->isSkolemFunction(n, sfi, cacheVal);
      // skolems v print as their original forms
      // v is (skolem W) where W is the original or original form of v
      Node wi = SkolemManager::getUnpurifiedForm(n);
      if (!wi.isNull() && wi != n)
      {
        Trace("alethe-conv")
            << "...to convert original form " << wi << std::endl;
        Node conv = convert(wi);
        // ignore purification skolems
        if (sfi != SkolemId::PURIFY)
        {
          d_skolemsList.push_back(n);
          d_skolems[n] = conv;
        }
        return conv;
      }
      if (sfi == SkolemId::QUANTIFIERS_SKOLEMIZE)
      {
        // create the witness term
        //
        //   (witness ((x_i T_i)) (exists ((x_i+1 T_i+1) ... (x_n T_n)) body))
        //
        // where the bound variables and the body come from the quantifier term
        // which must be the first element of cacheVal (which should be a list),
        // and i the second.
        Trace("alethe-conv")
            << ".. to build witness with index/quant: " << cacheVal[1] << " / "
            << cacheVal[0] << "\n";
        Assert(cacheVal.getKind() == Kind::SEXPR
               && cacheVal.getNumChildren() == 2);
        Node quant = cacheVal[0];
        Assert(quant.getKind() == Kind::FORALL);
        uint32_t index = -1;
        ProofRuleChecker::getUInt32(cacheVal[1], index);
        Assert(index < quant[0].getNumChildren());
        Node var = quant[0][index];
        // Since cvc5 *always* skolemize FORALLs, we generate the choice term
        // assuming it is gonna be introduced via a sko_forall rule, in which
        // case the body of the choice is negated, which means to have
        // universal quantification of the remaining variables in the choice
        // body, and the whole thing negated. Likewise, since during
        // Skolemization cvc5 will have negated the body of the original
        // quantifier, we need to revert that as well.
        Node body =
            (index == quant[0].getNumChildren() - 1
                 ? quant[1]
                 : d_nm->mkNode(Kind::FORALL,
                                d_nm->mkNode(Kind::BOUND_VAR_LIST,
                                             std::vector<Node>{
                                                 quant[0].begin() + index + 1,
                                                 quant[0].end()}),
                                quant[1]))
                .notNode();
        // we need to replace in the body all the free variables (i.e., from 0
        // to index) by their respective choice terms. To do this, we get
        // the skolems for each of these variables, retrieve their
        // conversions, and replace the variables by the conversions in body
        if (index > 0)
        {
          std::vector<Node> subs;
          for (size_t i = 0; i < index; ++i)
          {
            std::vector<Node> cacheVals{quant, d_nm->mkConstInt(Rational(i))};
            Node sk = sm->mkSkolemFunction(SkolemId::QUANTIFIERS_SKOLEMIZE,
                                           cacheVals);
            Assert(!sk.isNull());
            subs.push_back(d_defineSkolems ? sk : convert(sk));
          }
          body = body.substitute(quant[0].begin(),
                                 quant[0].begin() + index,
                                 subs.begin(),
                                 subs.end());
        }
        Node witness = d_nm->mkNode(
            Kind::WITNESS, d_nm->mkNode(Kind::BOUND_VAR_LIST, var), body);
        Trace("alethe-conv") << ".. witness: " << witness << "\n";
        witness = convert(witness);
        d_skolems[n] = witness;
        if (d_defineSkolems)
        {
          if (std::find(d_skolemsList.begin(), d_skolemsList.end(), n)
              == d_skolemsList.end())
          {
            d_skolemsList.push_back(n);
          }
          return n;
        }
        return witness;
      }
      if (sfi == SkolemId::ARRAY_DEQ_DIFF)
      {
        // create the witness term
        //
        //   (witness ((x T)) (or (= a b) (not (= (select a x) (select b x)))))
        //
        // where a and b come from cache and T is the index type of a (which
        // must be the same of b).
        Trace("alethe-conv")
            << ".. to build array diff choice with arrays: " << cacheVal[0]
            << " / " << cacheVal[1] << "\n";
        Assert(cacheVal.getKind() == Kind::SEXPR
               && cacheVal.getNumChildren() == 2);
        Node a = cacheVal[0];
        Assert(a.getType().isArray());
        Node b = cacheVal[1];
        Assert(b.getType().isArray());
        TypeNode indexType = a.getType().getArrayIndexType();
        // get index element of array
        Node var = NodeManager::mkBoundVar("x", indexType);
        Node eq = a.eqNode(b);
        Node select =
            d_nm->mkNode(Kind::NOT,
                         d_nm->mkNode(Kind::EQUAL,
                                      d_nm->mkNode(Kind::SELECT, a, var),
                                      d_nm->mkNode(Kind::SELECT, b, var)));
        Node body = d_nm->mkNode(Kind::OR, eq, select);
        Node choice = d_nm->mkNode(
            Kind::WITNESS, d_nm->mkNode(Kind::BOUND_VAR_LIST, var), body);
        choice = convert(choice);
        d_skolems[n] = choice;
        return choice;
      }
      if (sfi == SkolemId::GROUND_TERM)
      {
        // create the witness term (witness ((x T)) true) where T is the type of
        // the skolem. This skolem is introduced for example by enumerative
        // quantifier instantiation when no ground term exists in the formula of
        // the same type as the variable being instantiated. This is done only
        // once per type, so the formula in the body of the witness term is
        // nonrestrictive.
        TypeNode tn = n.getType();
        Trace("alethe-conv")
            << ".. to build stand-in for arbitrary ground term of type: " << tn
            << "\n";
        Node var = NodeManager::mkBoundVar("x", tn);
        Node trueNode = d_nm->mkConst(true);
        Node choice = d_nm->mkNode(
            Kind::WITNESS, d_nm->mkNode(Kind::BOUND_VAR_LIST, var), trueNode);
        choice = convert(choice);
        d_skolems[n] = choice;
        return choice;
      }
      std::stringstream ss;
      ss << "\"Proof unsupported by Alethe: contains Skolem (kind " << sfi
         << ", term " << n << "\"";
      d_error = ss.str();
      return Node::null();
    }
    case Kind::FORALL:
    {
      // remove patterns, if any
      return n.getNumChildren() == 3 ? d_nm->mkNode(Kind::FORALL, n[0], n[1])
                                     : n;
    }
    // we must make it to be printed with "choice", so we create an operator
    // with that name and the correct type and do a function application
    case Kind::WITNESS:
    {
      std::vector<TypeNode> childrenTypes;
      for (const Node& c : n)
      {
        childrenTypes.push_back(c.getType());
      }
      TypeNode fType = d_nm->mkFunctionType(childrenTypes, n.getType());
      Node choiceOp = mkInternalSymbol("choice", fType);
      Node converted = d_nm->mkNode(Kind::APPLY_UF, choiceOp, n[0], n[1]);
      Trace("alethe-conv") << ".. converted to choice: " << converted << "\n";
      return converted;
    }
    // other handled kinds but no-op in conversion. Everything else is
    // unsupported
    /* from builtin */
    case Kind::SORT_TYPE:
    case Kind::INSTANTIATED_SORT_TYPE:
    case Kind::UNINTERPRETED_SORT_VALUE:
    case Kind::BUILTIN:
    case Kind::EQUAL:
    case Kind::DISTINCT:
    case Kind::SEXPR:
    case Kind::TYPE_CONSTANT:
    case Kind::RAW_SYMBOL:
    case Kind::APPLY_INDEXED_SYMBOLIC:
    case Kind::APPLY_INDEXED_SYMBOLIC_OP:
    /* from booleans */
    case Kind::CONST_BOOLEAN:
    case Kind::NOT:
    case Kind::AND:
    case Kind::IMPLIES:
    case Kind::OR:
    case Kind::XOR:
    case Kind::ITE:
    /* from uf */
    case Kind::APPLY_UF:
    case Kind::FUNCTION_TYPE:
    case Kind::LAMBDA:
    case Kind::HO_APPLY:
    case Kind::FUNCTION_ARRAY_CONST:
    /* from arith */
    case Kind::ADD:
    case Kind::MULT:
    case Kind::NONLINEAR_MULT:
    case Kind::SUB:
    case Kind::NEG:
    case Kind::DIVISION:
    case Kind::INTS_DIVISION:
    case Kind::INTS_MODULUS:
    case Kind::ABS:
    case Kind::DIVISIBLE:
    case Kind::DIVISIBLE_OP:
    case Kind::CONST_RATIONAL:
    case Kind::CONST_INTEGER:
    case Kind::LT:
    case Kind::LEQ:
    case Kind::GT:
    case Kind::GEQ:
    case Kind::IS_INTEGER:
    case Kind::TO_INTEGER:
    case Kind::TO_REAL:
    case Kind::INTS_ISPOW2:
    case Kind::INTS_LOG2:
    case Kind::POW2:
    /* from arrays */
    case Kind::ARRAY_TYPE:
    case Kind::SELECT:
    case Kind::STORE:
    case Kind::ARRAY_LAMBDA:
    /* from quantifiers */
    case Kind::EXISTS:
    case Kind::BOUND_VAR_LIST:
    case Kind::INST_PATTERN:
    case Kind::INST_NO_PATTERN:
    case Kind::INST_ATTRIBUTE:
    case Kind::INST_POOL:
    case Kind::INST_ADD_TO_POOL:
    case Kind::SKOLEM_ADD_TO_POOL:
    case Kind::INST_PATTERN_LIST:
    {
      return n;
    }
    // BV, datatypes, strings, and constant array kinds are no-op in
    // conversion but are reported as unsupported when running in Alethe
    // testing mode.
    /* from arrays (constant arrays) */
    case Kind::STORE_ALL:
    /* from uf (BV-related) */
    case Kind::BITVECTOR_UBV_TO_INT:
    case Kind::INT_TO_BITVECTOR_OP:
    case Kind::INT_TO_BITVECTOR:
    /* from BV */
    case Kind::BITVECTOR_TYPE:
    case Kind::CONST_BITVECTOR:
    case Kind::BITVECTOR_SIZE:
    case Kind::CONST_BITVECTOR_SYMBOLIC:
    case Kind::BITVECTOR_CONCAT:
    case Kind::BITVECTOR_AND:
    case Kind::BITVECTOR_COMP:
    case Kind::BITVECTOR_OR:
    case Kind::BITVECTOR_XOR:
    case Kind::BITVECTOR_NOT:
    case Kind::BITVECTOR_NAND:
    case Kind::BITVECTOR_NOR:
    case Kind::BITVECTOR_XNOR:
    case Kind::BITVECTOR_MULT:
    case Kind::BITVECTOR_NEG:
    case Kind::BITVECTOR_ADD:
    case Kind::BITVECTOR_SUB:
    case Kind::BITVECTOR_UDIV:
    case Kind::BITVECTOR_UREM:
    case Kind::BITVECTOR_SDIV:
    case Kind::BITVECTOR_SMOD:
    case Kind::BITVECTOR_SREM:
    case Kind::BITVECTOR_ASHR:
    case Kind::BITVECTOR_LSHR:
    case Kind::BITVECTOR_SHL:
    case Kind::BITVECTOR_ULE:
    case Kind::BITVECTOR_ULT:
    case Kind::BITVECTOR_UGE:
    case Kind::BITVECTOR_UGT:
    case Kind::BITVECTOR_SLE:
    case Kind::BITVECTOR_SLT:
    case Kind::BITVECTOR_SGE:
    case Kind::BITVECTOR_SGT:
    case Kind::BITVECTOR_ULTBV:
    case Kind::BITVECTOR_SLTBV:
    case Kind::BITVECTOR_ACKERMANNIZE_UDIV:
    case Kind::BITVECTOR_ACKERMANNIZE_UREM:
    case Kind::BITVECTOR_BIT_OP:
    case Kind::BITVECTOR_EXTRACT_OP:
    case Kind::BITVECTOR_EXTRACT:
    case Kind::BITVECTOR_REPEAT_OP:
    case Kind::BITVECTOR_REPEAT:
    case Kind::BITVECTOR_ROTATE_LEFT_OP:
    case Kind::BITVECTOR_ROTATE_LEFT:
    case Kind::BITVECTOR_ROTATE_RIGHT_OP:
    case Kind::BITVECTOR_ROTATE_RIGHT:
    case Kind::BITVECTOR_SIGN_EXTEND_OP:
    case Kind::BITVECTOR_SIGN_EXTEND:
    case Kind::BITVECTOR_ZERO_EXTEND_OP:
    case Kind::BITVECTOR_ZERO_EXTEND:
    /* from datatypes */
    case Kind::CONSTRUCTOR_TYPE:
    case Kind::SELECTOR_TYPE:
    case Kind::TESTER_TYPE:
    case Kind::APPLY_CONSTRUCTOR:
    case Kind::APPLY_SELECTOR:
    case Kind::APPLY_TESTER:
    case Kind::DATATYPE_TYPE:
    case Kind::PARAMETRIC_DATATYPE:
    case Kind::TUPLE_TYPE:
    case Kind::APPLY_TYPE_ASCRIPTION:
    case Kind::ASCRIPTION_TYPE:
    case Kind::DT_SIZE:
    case Kind::DT_HEIGHT_BOUND:
    case Kind::DT_SIZE_BOUND:
    case Kind::MATCH:
    case Kind::MATCH_CASE:
    case Kind::MATCH_BIND_CASE:
    /* from strings */
    case Kind::STRING_CONCAT:
    case Kind::STRING_IN_REGEXP:
    case Kind::STRING_LENGTH:
    case Kind::STRING_SUBSTR:
    case Kind::STRING_CHARAT:
    case Kind::STRING_CONTAINS:
    case Kind::STRING_LT:
    case Kind::STRING_LEQ:
    case Kind::STRING_INDEXOF:
    case Kind::STRING_REPLACE:
    case Kind::STRING_REPLACE_ALL:
    case Kind::STRING_REPLACE_RE:
    case Kind::STRING_REPLACE_RE_ALL:
    case Kind::STRING_PREFIX:
    case Kind::STRING_SUFFIX:
    case Kind::STRING_IS_DIGIT:
    case Kind::STRING_ITOS:
    case Kind::STRING_STOI:
    case Kind::STRING_TO_CODE:
    case Kind::STRING_FROM_CODE:
    case Kind::STRING_UNIT:
    case Kind::CONST_STRING:
    case Kind::STRING_TO_REGEXP:
    case Kind::REGEXP_CONCAT:
    case Kind::REGEXP_UNION:
    case Kind::REGEXP_INTER:
    case Kind::REGEXP_DIFF:
    case Kind::REGEXP_STAR:
    case Kind::REGEXP_PLUS:
    case Kind::REGEXP_OPT:
    case Kind::REGEXP_RANGE:
    case Kind::REGEXP_COMPLEMENT:
    case Kind::REGEXP_NONE:
    case Kind::REGEXP_ALL:
    case Kind::REGEXP_ALLCHAR:
    case Kind::REGEXP_REPEAT_OP:
    case Kind::REGEXP_REPEAT:
    case Kind::REGEXP_LOOP_OP:
    case Kind::REGEXP_LOOP:
    case Kind::REGEXP_RV:
    {
      if (d_isTesting)
      {
        return recordUnsupportedKind(k);
      }
      return n;
    }
    case Kind::BOUND_VARIABLE:
    case Kind::VARIABLE:
    {
      // see if variable has a supported type. We need this check because in
      // some problems involving unsupported theories there are no operators,
      // just variables of unsupported type. Note that we need to consider the
      // subtypes of a given type as well.
      std::unordered_set<TypeNode> allTypes;
      TypeNode tn = n.getType();
      expr::getComponentTypes(tn, allTypes);
      std::vector<TypeNode> allTypesVec(allTypes.begin(), allTypes.end());
      collectTypes(allTypesVec, allTypes);
      TypeNode unsupported = TypeNode::null();
      for (const TypeNode& ttn : allTypes)
      {
        Kind tnk = ttn.getKind();
        Trace("test") << "Test " << ttn << ", kind " << tnk << "\n";
        switch (tnk)
        {
          case Kind::SORT_TYPE:
          case Kind::INSTANTIATED_SORT_TYPE:
          case Kind::FUNCTION_TYPE:
          case Kind::ARRAY_TYPE:
          {
            continue;
          }
          // BV and datatypes type kinds are unsupported under testing mode.
          case Kind::BITVECTOR_TYPE:
          case Kind::CONSTRUCTOR_TYPE:
          case Kind::SELECTOR_TYPE:
          case Kind::TESTER_TYPE:
          case Kind::ASCRIPTION_TYPE:
          {
            if (d_isTesting)
            {
              unsupported = ttn;
              break;
            }
            continue;
          }
          default:
          {
            // The supported constant types
            if (tnk == Kind::TYPE_CONSTANT)
            {
              switch (ttn.getConst<TypeConstant>())
              {
                case TypeConstant::SEXPR_TYPE:
                case TypeConstant::BOOLEAN_TYPE:
                case TypeConstant::REAL_TYPE:
                case TypeConstant::INTEGER_TYPE:
                {
                  continue;
                }
                // String and regexp types are unsupported under testing mode.
                case TypeConstant::STRING_TYPE:
                case TypeConstant::REGEXP_TYPE:
                {
                  if (!d_isTesting)
                  {
                    continue;
                  }
                  break;  // fallthrough to the error handling below
                }
                default:  // fallthrough to the error handling below
                  break;
              }
            }
            // Only regular datatypes (parametric or not) are supported, and
            // only outside testing mode.
            else if (!d_isTesting && ttn.isDatatype()
                     && !ttn.getDType().isCodatatype()
                     && (tnk == Kind::DATATYPE_TYPE
                         || tnk == Kind::PARAMETRIC_DATATYPE))
            {
              continue;
            }
            Trace("test") << "\tBad: " << ttn << ", kind " << tnk << "\n";
            unsupported = ttn;
            break;
          }
        }
      }
      if (unsupported.isNull())
      {
        return n;
      }
      Trace("alethe-conv") << "AletheNodeConverter: ...unsupported type\n";
      std::stringstream ss;
      ss << "\"Proof unsupported by Alethe: contains ";
      Kind utnk = unsupported.getKind();
      if (utnk == Kind::TYPE_CONSTANT)
      {
        ss << unsupported.getConst<TypeConstant>();
      }
      else if (unsupported.isDatatype())
      {
        ss << "non-standard datatype";
      }
      else
      {
        ss << utnk;
      }
      ss << "\"";
      d_error = ss.str();
      return Node::null();
    }
    default:
    {
      return recordUnsupportedKind(k);
    }
  }
  return n;
}

Node AletheNodeConverter::mkInternalSymbol(const std::string& name,
                                           TypeNode tn,
                                           bool useRawSym)
{
  std::pair<TypeNode, std::string> key(tn, name);
  std::map<std::pair<TypeNode, std::string>, Node>::iterator it =
      d_symbolsMap.find(key);
  if (it != d_symbolsMap.end())
  {
    return it->second;
  }
  Node sym = useRawSym ? NodeManager::mkRawSymbol(name, tn)
                       : NodeManager::mkBoundVar(name, tn);
  d_symbolsMap[key] = sym;
  return sym;
}

Node AletheNodeConverter::mkInternalSymbol(const std::string& name)
{
  return mkInternalSymbol(name, d_nm->sExprType());
}

const std::string& AletheNodeConverter::getError() { return d_error; }

Node AletheNodeConverter::getOriginalAssumption(Node n)
{
  auto it = d_convToOriginalAssumption.find(n);
  if (it != d_convToOriginalAssumption.end())
  {
    return it->second;
  }
  return n;
}

const std::map<Node, Node>& AletheNodeConverter::getSkolemDefinitions()
{
  return d_skolems;
}

const std::vector<Node>& AletheNodeConverter::getSkolemList()
{
  return d_skolemsList;
}

}  // namespace proof
}  // namespace cvc5::internal
