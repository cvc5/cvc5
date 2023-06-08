/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Class for constructing inductive datatypes that correspond to
 * grammars that encode syntactic restrictions for SyGuS.
 */

#include "theory/quantifiers/sygus/sygus_grammar_cons_new.h"

#include "expr/node_algorithm.h"
#include "theory/bv/theory_bv_utils.h"
#include "theory/strings/word.h"
#include "util/floatingpoint.h"
#include "util/string.h"
#include "options/quantifiers_options.h"
#include "expr/dtype.h"
#include "expr/dtype_cons.h"

using namespace cvc5::internal::kind;

namespace cvc5::internal {
namespace theory {
namespace quantifiers {

TypeNode SygusGrammarCons::mkDefaultSygusType(const Options& opts,
                                              const TypeNode& range,
                                              const Node& bvl)
{
  SygusGrammar g = mkDefaultGrammar(opts, range, bvl);
  return g.resolve();
}

TypeNode SygusGrammarCons::mkDefaultSygusType(const Options& opts,
                                              const TypeNode& range,
                                              const Node& bvl,
                                              const std::vector<Node>& trules)
{
  SygusGrammar g = mkDefaultGrammar(opts, range, bvl, trules);
  return g.resolve();
}

SygusGrammar SygusGrammarCons::mkDefaultGrammar(const Options& opts,
                                                const TypeNode& range,
                                                const Node& bvl)
{
  // default, include all variables as terminal rules
  std::vector<Node> trules;
  if (!bvl.isNull())
  {
    Assert(bvl.getKind() == BOUND_VARIABLE_LIST);
    trules.insert(trules.end(), bvl.begin(), bvl.end());
  }
  return mkDefaultGrammar(opts, range, bvl, trules);
}

SygusGrammar SygusGrammarCons::mkDefaultGrammar(const Options& opts,
                                                const TypeNode& range,
                                                const Node& bvl,
                                                const std::vector<Node>& trules)
{
  NodeManager* nm = NodeManager::currentNM();
  std::map<TypeNode, Node>::iterator it;
  SygusGrammar g = mkEmptyGrammar(opts, range, bvl, trules);
  std::map<TypeNode, Node> typeToNtSym = getTypeToNtSymMap(g);

  // get the non-terminal for Booleans
  Node ntSymBool;
  TypeNode btype = nm->booleanType();
  it = typeToNtSym.find(btype);
  if (it != typeToNtSym.end())
  {
    ntSymBool = it->second;
  }

  // add the terminal rules
  for (const Node& r : trules)
  {
    TypeNode rt = r.getType();
    it = typeToNtSym.find(rt);
    Assert(it != typeToNtSym.end());
    g.addRule(it->second, r);
  }

  for (const std::pair<const TypeNode, Node>& gr : typeToNtSym)
  {
    // add rules for each type
    addDefaultRulesToInternal(opts, g, gr.second, typeToNtSym);
    // add predicates for the type to the Boolean grammar if it exists
    if (!ntSymBool.isNull() && !gr.first.isBoolean())
    {
      addDefaultPredicateRulesToInternal(
          opts, g, gr.second, ntSymBool, typeToNtSym);
    }
  }
  return g;
}

SygusGrammar SygusGrammarCons::mkEmptyGrammar(const Options& opts,
                                              const TypeNode& range,
                                              const Node& bvl,
                                              const std::vector<Node>& trules)
{
  NodeManager* nm = NodeManager::currentNM();
  // get the variables
  std::vector<Node> vars;
  if (!bvl.isNull())
  {
    Assert(bvl.getKind() == BOUND_VARIABLE_LIST);
    vars.insert(vars.end(), bvl.begin(), bvl.end());
  }
  // collect the types we are considering, which is all component types of
  // the range type and the initial terminal rules. We also always include
  // Bool.
  std::unordered_set<TypeNode> types;
  for (const Node& r : trules)
  {
    expr::getComponentTypes(r.getType(), types, true);
  }
  expr::getComponentTypes(range, types, true);
  // always include Boolean
  TypeNode btype = nm->booleanType();
  types.insert(btype);
  // the range type comes first
  std::vector<TypeNode> tvec;
  tvec.push_back(range);
  for (const TypeNode& t : types)
  {
    if (t != range)
    {
      tvec.push_back(t);
    }
  }

  // construct the non-terminals
  std::vector<Node> ntSyms;
  for (const TypeNode& t : tvec)
  {
    Node a = nm->mkBoundVar("A", t);
    ntSyms.push_back(a);
  }

  // contruct the grammar
  SygusGrammar ret(vars, ntSyms);
  return ret;
}

void SygusGrammarCons::addDefaultRulesTo(const Options& opts,
                                         SygusGrammar& g,
                                         const Node& ntSym)
{
  // recompute mapping from types to non-terminal symbols
  std::map<TypeNode, Node> typeToNtSym = getTypeToNtSymMap(g);
  addDefaultRulesToInternal(opts, g, ntSym, typeToNtSym);
}

void SygusGrammarCons::addDefaultPredicateRulesTo(const Options& opts,
                                                  SygusGrammar& g,
                                                  const Node& ntSym,
                                                  const Node& ntSymBool)
{
  // recompute mapping from types to non-terminal symbols
  std::map<TypeNode, Node> typeToNtSym = getTypeToNtSymMap(g);
  addDefaultPredicateRulesToInternal(opts, g, ntSym, ntSymBool, typeToNtSym);
}

void SygusGrammarCons::addDefaultRulesToInternal(
    const Options& opts,
    SygusGrammar& g,
    const Node& ntSym,
    const std::map<TypeNode, Node>& typeToNtSym)
{
  TypeNode tn = ntSym.getType();
  std::vector<Node> prevRules = g.getRulesFor(ntSym);
  // add constants
  options::SygusGrammarConsMode tsgcm = opts.quantifiers.sygusGrammarConsMode;
  if (tsgcm == options::SygusGrammarConsMode::ANY_TERM
      || tsgcm == options::SygusGrammarConsMode::ANY_TERM_CONCISE)
  {
    // If the type does not support any term, we do any constant instead.
    // We also fall back on any constant construction if the type has no
    // constructors at this point (e.g. it simply encodes all constants).
    if (!tn.isRealOrInt())
    {
      tsgcm = options::SygusGrammarConsMode::ANY_CONST;
    }
  }
  std::vector<Node> consts;
  mkSygusConstantsForType(tn, consts);
  if (tsgcm == options::SygusGrammarConsMode::ANY_CONST)
  {
    // Use the any constant constructor. Notice that for types that don't
    // have constants (e.g. uninterpreted or function types), we don't add
    // this constructor.
    if (!consts.empty())
    {
      g.addAnyConstant(ntSym, tn);
    }
  }
  else
  {
    for (const Node& c : consts)
    {
      // if not already there?
      if (std::find(prevRules.begin(), prevRules.end(), c)==prevRules.end())
      {
        g.addRule(ntSym, c);
      }
    }
  }
NodeManager * nm = NodeManager::currentNM();
  // add the operators
  if (tn.isRealOrInt())
  {
    // Add ADD, SUB
    Kind kinds[2] = {ADD, SUB};
    for (const Kind kind : kinds)
    {
      Trace("sygus-grammar-def") << "...add for " << kind << std::endl;
      std::vector<TypeNode> cargsOp;
      cargsOp.push_back(tn);
      cargsOp.push_back(tn);
      addRuleTo(g, typeToNtSym, kind, cargsOp);
    }
    /*
    if (!tn.isInteger())
    {
      Trace("sygus-grammar-def")
          << "  ...create auxiliary Positive Integers grammar\n";
      // Creating type for positive integral reals. Notice we can't use the
      // any constant constructor here, since it admits zero.
      std::stringstream ss;
      ss << fun << "_PosIReal";
      std::string posIRealName = ss.str();
      // make unresolved type
      TypeNode unresPosIReal = mkUnresolvedType(posIRealName);
      tnypes.push_back(unresPosIReal);
      // make data type for positive constant integral reals
      sdts.push_back(SygusDatatypeGenerator(posIRealName));
      // Add operator 1
      Trace("sygus-grammar-def") << "\t...add for 1.0 to PosIReal\n";
      std::vector<TypeNode> cargsEmpty;
      sdts.back().addConstructor(
          nm->mkConstReal(Rational(1)), "1", cargsEmpty);
      // Add operator ADD
      Kind kind = ADD;
      Trace("sygus-grammar-def") << "\t...add for ADD to PosIReal\n";
      std::vector<TypeNode> cargsPlus;
      cargsPlus.push_back(unresPosIReal);
      cargsPlus.push_back(unresPosIReal);
      sdts.back().addConstructor(kind, cargsPlus);
      sdts.back().d_sdt.initializeDatatype(tn, bvl, true, true);
      Trace("sygus-grammar-def")
          << "  ...built datatype " << sdts.back().d_sdt.getDatatype() << " ";
      // Adding division at root
      kind = DIVISION;
      Trace("sygus-grammar-def") << "\t...add for " << kind << std::endl;
      std::vector<TypeNode> cargsDiv;
      cargsDiv.push_back(tn);
      cargsDiv.push_back(unresPosIReal);
      g.addRule(ntSym, kind, cargsDiv);
    }
    */
  }
  else if (tn.isBitVector())
  {
    // unary ops
    std::vector<Kind> un_kinds = {BITVECTOR_NOT, BITVECTOR_NEG};
    std::vector<TypeNode> cargsUnary;
    cargsUnary.push_back(tn);
    for (const Kind kind : un_kinds)
    {
      Trace("sygus-grammar-def") << "...add for " << kind << std::endl;
      addRuleTo(g, typeToNtSym, kind, cargsUnary);
    }
    // binary ops
    std::vector<Kind> bin_kinds = {BITVECTOR_AND,
                                    BITVECTOR_OR,
                                    BITVECTOR_XOR,
                                    BITVECTOR_ADD,
                                    BITVECTOR_SUB,
                                    BITVECTOR_MULT,
                                    BITVECTOR_UDIV,
                                    BITVECTOR_UREM,
                                    BITVECTOR_SDIV,
                                    BITVECTOR_SREM,
                                    BITVECTOR_SHL,
                                    BITVECTOR_LSHR,
                                    BITVECTOR_ASHR};
    std::vector<TypeNode> cargsBinary;
    cargsBinary.push_back(tn);
    cargsBinary.push_back(tn);
    for (const Kind kind : bin_kinds)
    {
      Trace("sygus-grammar-def") << "...add for " << kind << std::endl;
      addRuleTo(g, typeToNtSym, kind, cargsBinary);
    }
  }
  else if (tn.isFloatingPoint())
  {
    // unary ops
    std::vector<Kind> unary_kinds = {
        FLOATINGPOINT_ABS,
        FLOATINGPOINT_NEG,
    };
    std::vector<TypeNode> cargs = {tn};
    for (const Kind kind : unary_kinds)
    {
      Trace("sygus-grammar-def") << "...add for " << kind << std::endl;
      addRuleTo(g, typeToNtSym, kind, cargs);
    }
    // binary ops
    {
      const Kind kind = FLOATINGPOINT_REM;
      cargs.push_back(tn);
      Trace("sygus-grammar-def") << "...add for " << kind << std::endl;
      addRuleTo(g, typeToNtSym, kind, cargs);
    }
    // binary ops with RM
    std::vector<Kind> binary_rm_kinds = {
        FLOATINGPOINT_SQRT,
        FLOATINGPOINT_RTI,
    };
    TypeNode rmType = nm->roundingModeType();
    Assert(std::find(types.begin(), types.end(), rmType) != types.end());
    std::vector<TypeNode> cargs_rm = {rmType, tn};
    for (const Kind kind : binary_rm_kinds)
    {
      Trace("sygus-grammar-def") << "...add for " << kind << std::endl;
      addRuleTo(g, typeToNtSym, kind, cargs_rm);
    }
    // ternary ops with RM
    std::vector<Kind> ternary_rm_kinds = {
        FLOATINGPOINT_ADD,
        FLOATINGPOINT_SUB,
        FLOATINGPOINT_MULT,
        FLOATINGPOINT_DIV,
    };
    cargs_rm.push_back(tn);
    for (const Kind kind : ternary_rm_kinds)
    {
      Trace("sygus-grammar-def") << "...add for " << kind << std::endl;
      addRuleTo(g, typeToNtSym, kind, cargs_rm);
    }
    // quaternary ops
    {
      cargs_rm.push_back(tn);
      const Kind kind = FLOATINGPOINT_FMA;
      Trace("sygus-grammar-def") << "...add for " << kind << std::endl;
      addRuleTo(g, typeToNtSym, kind, cargs_rm);
    }
  }
  else if (tn.isStringLike())
  {
    // concatenation
    std::vector<TypeNode> cargsBinary;
    cargsBinary.push_back(tn);
    cargsBinary.push_back(tn);
    addRuleTo(g, typeToNtSym, STRING_CONCAT, cargsBinary);
    // length
    std::vector<TypeNode> cargsLen;
    cargsLen.push_back(tn);
    addRuleTo(g, typeToNtSym, STRING_LENGTH, cargsLen);
    if (tn.isSequence())
    {
      TypeNode etype = tn.getSequenceElementType();
      Trace("sygus-grammar-def") << "...add for seq.unit" << std::endl;
      std::vector<TypeNode> cargsSeqUnit;
      cargsSeqUnit.push_back(etype);
      addRuleTo(g, typeToNtSym, SEQ_UNIT, cargsSeqUnit);
    }
  }
  else if (tn.isArray())
  {
    Trace("sygus-grammar-def")
        << "...building for array type " << tn << "\n";
    TypeNode indexType = tn.getArrayIndexType();
    TypeNode elemType = tn.getArrayConstituentType();
    Trace("sygus-grammar-def")
        << "......finding unres type for index type " << indexType << "\n";
    // add (store ArrayType IndexType ConstituentType)
    Trace("sygus-grammar-def") << "...add for STORE\n";
    std::vector<TypeNode> cargsStore;
    cargsStore.push_back(tn);
    cargsStore.push_back(indexType);
    cargsStore.push_back(elemType);
    addRuleTo(g, typeToNtSym, STORE, cargsStore);
    // add to constituent type : (select ArrayType IndexType)
    Trace("sygus-grammar-def") << "...add select for constituent type"
                                << elemType << "\n";
    std::vector<TypeNode> cargsSelect;
    cargsSelect.push_back(tn);
    cargsSelect.push_back(indexType);
    addRuleTo(g, typeToNtSym, SELECT, cargsSelect);
  }
  else if (tn.isSet())
  {
    TypeNode etype = tn.getSetElementType();
    // add for singleton
    Trace("sygus-grammar-def") << "...add for singleton" << std::endl;
    std::vector<TypeNode> cargsSingleton;
    cargsSingleton.push_back(etype);
    addRuleTo(g, typeToNtSym, SET_SINGLETON, cargsSingleton);
    // add for union, difference, intersection
    std::vector<Kind> bin_kinds = {SET_UNION, SET_INTER, SET_MINUS};
    std::vector<TypeNode> cargsBinary;
    cargsBinary.push_back(tn);
    cargsBinary.push_back(tn);
    for (const Kind kind : bin_kinds)
    {
      Trace("sygus-grammar-def") << "...add for " << kind << std::endl;
      addRuleTo(g, typeToNtSym, kind, cargsBinary);
    }
  }
  else if (tn.isDatatype())
  {
    Trace("sygus-grammar-def") << "...add for constructors" << std::endl;
    const DType& dt = tn.getDType();
    for (unsigned l = 0, size_l = dt.getNumConstructors(); l < size_l; ++l)
    {
      Trace("sygus-grammar-def") << "...for " << dt[l].getName() << std::endl;
      Node cop = dt[l].getConstructor();
      TypeNode tspec = dt[l].getInstantiatedConstructorType(tn);
      // must specialize if a parametric datatype
      if (dt.isParametric())
      {
        cop = dt[l].getInstantiatedConstructor(tn);
      }
      std::vector<TypeNode> cargsCons;
      Trace("sygus-grammar-def") << "...add for selectors" << std::endl;
      // iterate over the arguments of the specialized constructor type,
      // which accounts for parametric datatypes
      std::vector<TypeNode> tsargs = tspec.getArgTypes();
      for (size_t j = 0, size_j = tsargs.size(); j < size_j; ++j)
      {
        Trace("sygus-grammar-def")
            << "...for " << dt[l][j].getName() << std::endl;
        cargsCons.push_back(tsargs[j]);
        // add to the selector type the selector operator
        std::vector<TypeNode> cargsSel;
        cargsSel.push_back(tn);
        Node sel = dt[l][j].getSelector();
        addRuleTo(g, typeToNtSym, APPLY_SELECTOR, sel, cargsSel);
      }
      addRuleTo(g, typeToNtSym, APPLY_CONSTRUCTOR, cop, cargsCons);
    }
  }
}

void SygusGrammarCons::addDefaultPredicateRulesToInternal(
    const Options& opts,
    SygusGrammar& g,
    const Node& ntSym,
    const Node& ntSymBool,
    const std::map<TypeNode, Node>& typeToNtSym)
{
  Assert(!ntSym.getType().isBoolean());
  Assert(ntSymBool.getType().isBoolean());
  // TODO
}

void SygusGrammarCons::mkSygusConstantsForType(const TypeNode& type,
                                               std::vector<Node>& ops)
{
  NodeManager* nm = NodeManager::currentNM();
  if (type.isRealOrInt())
  {
    ops.push_back(nm->mkConstRealOrInt(type, Rational(0)));
    ops.push_back(nm->mkConstRealOrInt(type, Rational(1)));
  }
  else if (type.isBitVector())
  {
    unsigned size = type.getBitVectorSize();
    ops.push_back(bv::utils::mkZero(size));
    ops.push_back(bv::utils::mkOne(size));
  }
  else if (type.isBoolean())
  {
    ops.push_back(nm->mkConst(true));
    ops.push_back(nm->mkConst(false));
  }
  else if (type.isStringLike())
  {
    ops.push_back(strings::Word::mkEmptyWord(type));
    if (type.isString())  // string-only
    {
      // Dummy character "A". This is not necessary for sequences which
      // have the generic constructor seq.unit.
      ops.push_back(nm->mkConst(String("A")));
    }
  }
  else if (type.isArray() || type.isSet())
  {
    // generate constant array over the first element of the constituent type
    Node c = nm->mkGroundTerm(type);
    // note that c should never contain an uninterpreted sort value
    Assert(!expr::hasSubtermKind(UNINTERPRETED_SORT_VALUE, c));
    ops.push_back(c);
  }
  else if (type.isRoundingMode())
  {
    ops.push_back(nm->mkConst(RoundingMode::ROUND_NEAREST_TIES_TO_AWAY));
    ops.push_back(nm->mkConst(RoundingMode::ROUND_NEAREST_TIES_TO_EVEN));
    ops.push_back(nm->mkConst(RoundingMode::ROUND_TOWARD_NEGATIVE));
    ops.push_back(nm->mkConst(RoundingMode::ROUND_TOWARD_POSITIVE));
    ops.push_back(nm->mkConst(RoundingMode::ROUND_TOWARD_ZERO));
  }
  else if (type.isFloatingPoint())
  {
    FloatingPointSize fp_size(type.getFloatingPointExponentSize(),
                              type.getFloatingPointSignificandSize());
    ops.push_back(nm->mkConst(FloatingPoint::makeNaN(fp_size)));
    ops.push_back(nm->mkConst(FloatingPoint::makeInf(fp_size, true)));
    ops.push_back(nm->mkConst(FloatingPoint::makeInf(fp_size, false)));
    ops.push_back(nm->mkConst(FloatingPoint::makeZero(fp_size, true)));
    ops.push_back(nm->mkConst(FloatingPoint::makeZero(fp_size, false)));
    ops.push_back(nm->mkConst(FloatingPoint::makeMinSubnormal(fp_size, true)));
    ops.push_back(nm->mkConst(FloatingPoint::makeMinSubnormal(fp_size, false)));
    ops.push_back(nm->mkConst(FloatingPoint::makeMaxSubnormal(fp_size, true)));
    ops.push_back(nm->mkConst(FloatingPoint::makeMaxSubnormal(fp_size, false)));
    ops.push_back(nm->mkConst(FloatingPoint::makeMinNormal(fp_size, true)));
    ops.push_back(nm->mkConst(FloatingPoint::makeMinNormal(fp_size, false)));
    ops.push_back(nm->mkConst(FloatingPoint::makeMaxNormal(fp_size, true)));
    ops.push_back(nm->mkConst(FloatingPoint::makeMaxNormal(fp_size, false)));
  }
}

std::map<TypeNode, Node> SygusGrammarCons::getTypeToNtSymMap(
    const SygusGrammar& g)
{
  std::map<TypeNode, Node> typeToNtSym;
  const std::vector<Node>& ntSyms = g.getNtSyms();
  for (const Node& s : ntSyms)
  {
    typeToNtSym[s.getType()] = s;
  }
  return typeToNtSym;
}

bool SygusGrammarCons::addRuleTo(SygusGrammar& g, const std::map<TypeNode, Node>& typeToNtSym, Kind k, const std::vector<TypeNode>& args)
{
  Node op;
  return addRuleTo(g, typeToNtSym, k, op, args);
}

bool SygusGrammarCons::addRuleTo(SygusGrammar& g, const std::map<TypeNode, Node>& typeToNtSym, Kind k, const Node& op, const std::vector<TypeNode>& args)
{
  std::map<TypeNode, Node>::const_iterator it;
  std::vector<Node> children;
  if (!op.isNull())
  {
    children.push_back(op);
  }
  for (const TypeNode& a : args)
  {
    it = typeToNtSym.find(a);
    if (it==typeToNtSym.end())
    {
      return false;
    }
    children.push_back(it->second);
  }
  Node rule = NodeManager::currentNM()->mkNode(k, children);
  TypeNode rtn = rule.getType();
  it = typeToNtSym.find(rtn);
  if (it==typeToNtSym.end())
  {
    return false;
  }
  g.addRule(it->second, rule);
  return true;
}

}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal
