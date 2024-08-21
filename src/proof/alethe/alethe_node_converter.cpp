/******************************************************************************
 * Top contributors (to current version):
 *   Haniel Barbosa, Aina Niemetz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2024 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Implementation of Alethe node conversion
 */

#include "proof/alethe/alethe_node_converter.h"

#include "expr/node_algorithm.h"
#include "expr/skolem_manager.h"
#include "proof/proof_rule_checker.h"
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

Node AletheNodeConverter::postConvert(Node n)
{
  NodeManager* nm = NodeManager::currentNM();
  Kind k = n.getKind();
  switch (k)
  {
    case Kind::BITVECTOR_BIT:
    {
      std::stringstream ss;
      ss << "(_ @bitOf " << n.getOperator().getConst<BitVectorBit>().d_bitIndex
         << ")";
      TypeNode fType = nm->mkFunctionType(n[0].getType(), n.getType());
      Node op = mkInternalSymbol(ss.str(), fType, true);
      Node converted = nm->mkNode(Kind::APPLY_UF, op, n[0]);
      return converted;
    }
    case Kind::BITVECTOR_FROM_BOOLS:
    {
      std::vector<Node> children;
      std::vector<TypeNode> childrenTypes;
      for (const Node& c : n)
      {
        childrenTypes.push_back(c.getType());
        children.push_back(c);
      }
      TypeNode fType = nm->mkFunctionType(childrenTypes, n.getType());
      Node op = mkInternalSymbol("@bbT", fType, true);
      children.insert(children.begin(), op);
      Node converted = nm->mkNode(Kind::APPLY_UF, children);
      return converted;
    }
    case Kind::BITVECTOR_EAGER_ATOM:
    {
      return n[0];
    }
    case Kind::DIVISION_TOTAL:
    {
      return nm->mkNode(Kind::DIVISION, n[0], n[1]);
    }
    case Kind::INTS_DIVISION_TOTAL:
    {
      return nm->mkNode(Kind::INTS_DIVISION, n[0], n[1]);
    }
    case Kind::INTS_MODULUS_TOTAL:
    {
      return nm->mkNode(Kind::INTS_MODULUS, n[0], n[1]);
    }
    case Kind::SKOLEM:
    {
      Trace("alethe-conv") << "AletheNodeConverter: handling skolem " << n
                           << "\n";
      SkolemManager* sm = nm->getSkolemManager();
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
          d_skolems[n] = conv;
        }
        return conv;
      }
      // create the witness term (witness ((x_i T_i)) (exists ((x_i+1 T_i+1)
      // ... (x_n T_n)) body), where the bound variables and the body come from
      // the quantifier term which must be the first element of cacheVal (which
      // should be a list), and i the second.
      if (sfi == SkolemId::QUANTIFIERS_SKOLEMIZE)
      {
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
                 : nm->mkNode(
                     Kind::FORALL,
                     nm->mkNode(Kind::BOUND_VAR_LIST,
                                std::vector<Node>{quant[0].begin() + index + 1,
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
            std::vector<Node> cacheVals{quant, nm->mkConstInt(Rational(i))};
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
        Node witness = nm->mkNode(
            Kind::WITNESS, nm->mkNode(Kind::BOUND_VAR_LIST, var), body);
        Trace("alethe-conv") << ".. witness: " << witness << "\n";
        witness = convert(witness);
        if (d_defineSkolems)
        {
          d_skolemsAux[n] = witness;
          if (index == quant[0].getNumChildren() - 1)
          {
            Trace("alethe-conv")
                << "....populate map from aux : " << d_skolemsAux << "\n";
            for (size_t i = index + 1; i > 0; --i)
            {
              std::vector<Node> cacheVals{quant,
                                          nm->mkConstInt(Rational(i - 1))};
              Node sk = sm->mkSkolemFunction(SkolemId::QUANTIFIERS_SKOLEMIZE,
                                             cacheVals);
              Assert(!sk.isNull());
              Assert(d_skolemsAux.find(sk) != d_skolemsAux.end())
                  << "Could not find sk " << sk;
              d_skolems[sk] = d_skolemsAux[sk];
            }
            d_skolemsAux.clear();
          }
          return n;
        }
        d_skolems[n] = witness;
        return witness;
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
      return n.getNumChildren() == 3 ? nm->mkNode(Kind::FORALL, n[0], n[1]) : n;
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
      TypeNode fType = nm->mkFunctionType(childrenTypes, n.getType());
      Node choiceOp = mkInternalSymbol("choice", fType);
      Node converted = nm->mkNode(Kind::APPLY_UF, choiceOp, n[0], n[1]);
      Trace("alethe-conv") << ".. converted to choice: " << converted << "\n";
      return converted;
    }
    /* from uf */
    case Kind::CARDINALITY_CONSTRAINT_OP:
    case Kind::CARDINALITY_CONSTRAINT:
    case Kind::COMBINED_CARDINALITY_CONSTRAINT_OP:
    case Kind::COMBINED_CARDINALITY_CONSTRAINT:
      /* from arith */
    case Kind::EXPONENTIAL:
    case Kind::SINE:
    case Kind::COSINE:
    case Kind::TANGENT:
    case Kind::COSECANT:
    case Kind::SECANT:
    case Kind::COTANGENT:
    case Kind::ARCSINE:
    case Kind::ARCCOSINE:
    case Kind::ARCTANGENT:
    case Kind::ARCCOSECANT:
    case Kind::ARCSECANT:
    case Kind::ARCCOTANGENT:
    case Kind::SQRT:
    case Kind::PI:
    case Kind::REAL_ALGEBRAIC_NUMBER_OP:
    case Kind::REAL_ALGEBRAIC_NUMBER:
    case Kind::INDEXED_ROOT_PREDICATE_OP:
    case Kind::INDEXED_ROOT_PREDICATE:
    case Kind::IAND_OP:
    case Kind::IAND:
    /* from ff */
    case Kind::FINITE_FIELD_TYPE:
    case Kind::CONST_FINITE_FIELD:
    case Kind::FINITE_FIELD_MULT:
    case Kind::FINITE_FIELD_NEG:
    case Kind::FINITE_FIELD_ADD:
    case Kind::FINITE_FIELD_BITSUM:
    /* from fp */
    case Kind::CONST_FLOATINGPOINT:
    case Kind::CONST_ROUNDINGMODE:
    case Kind::FLOATINGPOINT_TYPE:
    case Kind::FLOATINGPOINT_FP:
    case Kind::FLOATINGPOINT_EQ:
    case Kind::FLOATINGPOINT_ABS:
    case Kind::FLOATINGPOINT_NEG:
    case Kind::FLOATINGPOINT_ADD:
    case Kind::FLOATINGPOINT_SUB:
    case Kind::FLOATINGPOINT_MULT:
    case Kind::FLOATINGPOINT_DIV:
    case Kind::FLOATINGPOINT_FMA:
    case Kind::FLOATINGPOINT_SQRT:
    case Kind::FLOATINGPOINT_REM:
    case Kind::FLOATINGPOINT_RTI:
    case Kind::FLOATINGPOINT_MIN:
    case Kind::FLOATINGPOINT_MAX:
    case Kind::FLOATINGPOINT_MIN_TOTAL:
    case Kind::FLOATINGPOINT_MAX_TOTAL:
    case Kind::FLOATINGPOINT_LEQ:
    case Kind::FLOATINGPOINT_LT:
    case Kind::FLOATINGPOINT_GEQ:
    case Kind::FLOATINGPOINT_GT:
    case Kind::FLOATINGPOINT_IS_NORMAL:
    case Kind::FLOATINGPOINT_IS_SUBNORMAL:
  case Kind::FLOATINGPOINT_IS_ZERO:
  case Kind::FLOATINGPOINT_IS_INF:
  case Kind::FLOATINGPOINT_IS_NAN:
  case Kind::FLOATINGPOINT_IS_NEG:
  case Kind::FLOATINGPOINT_IS_POS:
  case Kind::FLOATINGPOINT_TO_FP_FROM_IEEE_BV_OP:
  case Kind::FLOATINGPOINT_TO_FP_FROM_IEEE_BV:
  case Kind::FLOATINGPOINT_TO_FP_FROM_FP_OP:
  case Kind::FLOATINGPOINT_TO_FP_FROM_FP:
  case Kind::FLOATINGPOINT_TO_FP_FROM_REAL_OP:
  case Kind::FLOATINGPOINT_TO_FP_FROM_REAL:
  case Kind::FLOATINGPOINT_TO_FP_FROM_SBV_OP:
  case Kind::FLOATINGPOINT_TO_FP_FROM_SBV:
  case Kind::FLOATINGPOINT_TO_FP_FROM_UBV_OP:
  case Kind::FLOATINGPOINT_TO_FP_FROM_UBV:
  case Kind::FLOATINGPOINT_TO_UBV_OP:
  case Kind::FLOATINGPOINT_TO_UBV:
  case Kind::FLOATINGPOINT_TO_UBV_TOTAL_OP:
  case Kind::FLOATINGPOINT_TO_UBV_TOTAL:
  case Kind::FLOATINGPOINT_TO_SBV_OP:
  case Kind::FLOATINGPOINT_TO_SBV:
  case Kind::FLOATINGPOINT_TO_SBV_TOTAL_OP:
  case Kind::FLOATINGPOINT_TO_SBV_TOTAL:
  case Kind::FLOATINGPOINT_TO_REAL:
  case Kind::FLOATINGPOINT_TO_REAL_TOTAL:
  case Kind::FLOATINGPOINT_COMPONENT_NAN:
  case Kind::FLOATINGPOINT_COMPONENT_INF:
  case Kind::FLOATINGPOINT_COMPONENT_ZERO:
  case Kind::FLOATINGPOINT_COMPONENT_SIGN:
  case Kind::FLOATINGPOINT_COMPONENT_EXPONENT:
  case Kind::FLOATINGPOINT_COMPONENT_SIGNIFICAND:
  case Kind::ROUNDINGMODE_BITBLAST:
  /* from arrays */
  case Kind::EQ_RANGE:
  /* from datatypes */
  case Kind::APPLY_UPDATER:
  case Kind::UPDATER_TYPE:
  case Kind::TUPLE_TYPE:
  case Kind::DT_SYGUS_BOUND:
  case Kind::DT_SYGUS_EVAL:
  case Kind::TUPLE_PROJECT_OP:
  case Kind::TUPLE_PROJECT:
  case Kind::CODATATYPE_BOUND_VARIABLE:
  case Kind::NULLABLE_TYPE:
  case Kind::NULLABLE_LIFT:
  /* from sep */
  case Kind::SEP_NIL:
  case Kind::SEP_EMP:
  case Kind::SEP_PTO:
  case Kind::SEP_STAR:
  case Kind::SEP_WAND:
  case Kind::SEP_LABEL:
  /* from sets */
  case Kind::SET_EMPTY:
  case Kind::SET_TYPE:
  case Kind::SET_UNION:
  case Kind::SET_INTER:
  case Kind::SET_MINUS:
  case Kind::SET_SUBSET:
  case Kind::SET_MEMBER:
  case Kind::SET_SINGLETON:
  case Kind::SET_INSERT:
  case Kind::SET_CARD:
  case Kind::SET_COMPLEMENT:
  case Kind::SET_UNIVERSE:
  case Kind::SET_COMPREHENSION:
  case Kind::SET_CHOOSE:
  case Kind::SET_IS_SINGLETON:
  case Kind::SET_MAP:
  case Kind::SET_FILTER:
  case Kind::SET_FOLD:
  case Kind::RELATION_GROUP_OP:
  case Kind::RELATION_GROUP:
  case Kind::RELATION_AGGREGATE_OP:
  case Kind::RELATION_AGGREGATE:
  case Kind::RELATION_PROJECT_OP:
  case Kind::RELATION_PROJECT:
  case Kind::RELATION_JOIN:
  case Kind::RELATION_PRODUCT:
  case Kind::RELATION_TRANSPOSE:
  case Kind::RELATION_TCLOSURE:
  case Kind::RELATION_JOIN_IMAGE:
  case Kind::RELATION_IDEN:
  /* from bags */
  case Kind::BAG_EMPTY:
  case Kind::BAG_TYPE:
  case Kind::BAG_UNION_MAX:
  case Kind::BAG_UNION_DISJOINT:
  case Kind::BAG_INTER_MIN:
  case Kind::BAG_DIFFERENCE_SUBTRACT:
  case Kind::BAG_DIFFERENCE_REMOVE:
  case Kind::BAG_SUBBAG:
  case Kind::BAG_COUNT:
  case Kind::BAG_MEMBER:
  case Kind::BAG_SETOF:
  case Kind::BAG_MAKE:
  case Kind::BAG_CARD:
  case Kind::BAG_CHOOSE:
  case Kind::BAG_MAP:
  case Kind::BAG_FILTER:
  case Kind::BAG_FOLD:
  case Kind::BAG_PARTITION:
  case Kind::TABLE_PRODUCT:
  case Kind::TABLE_PROJECT_OP:
  case Kind::TABLE_PROJECT:
  case Kind::TABLE_AGGREGATE_OP:
  case Kind::TABLE_AGGREGATE:
  case Kind::TABLE_JOIN_OP:
  case Kind::TABLE_JOIN:
  case Kind::TABLE_GROUP_OP:
  case Kind::TABLE_GROUP:
  {
    std::stringstream ss;
    ss << "\"Proof unsupported by Alethe: contains operator " << k << "\"";
    d_error = ss.str();
    return Node::null();
    }
    default:
    {
      return n;
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
  NodeManager* nm = NodeManager::currentNM();
  Node sym = useRawSym ? nm->mkRawSymbol(name, tn) : nm->mkBoundVar(name, tn);
  d_symbolsMap[key] = sym;
  return sym;
}

Node AletheNodeConverter::mkInternalSymbol(const std::string& name)
{
  return mkInternalSymbol(name, NodeManager::currentNM()->sExprType());
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

}  // namespace proof
}  // namespace cvc5::internal
