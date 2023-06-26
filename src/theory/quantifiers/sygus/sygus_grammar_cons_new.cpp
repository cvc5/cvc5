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

#include <sstream>

#include "expr/dtype.h"
#include "expr/dtype_cons.h"
#include "expr/node_algorithm.h"
#include "options/quantifiers_options.h"
#include "theory/bv/theory_bv_utils.h"
#include "theory/strings/word.h"
#include "util/floatingpoint.h"
#include "util/string.h"

using namespace cvc5::internal::kind;

namespace cvc5::internal {
namespace theory {
namespace quantifiers {

/** Number of stages of grammar construction */
const size_t s_nstages = 2;

TypeNode SygusGrammarCons::mkDefaultSygusType(const Options& opts,
                                              const TypeNode& range,
                                              const Node& bvl)
{
  SygusGrammar g = mkDefaultGrammar(opts, range, bvl);
  return g.resolve(true);
}

TypeNode SygusGrammarCons::mkDefaultSygusType(const Options& opts,
                                              const TypeNode& range,
                                              const Node& bvl,
                                              const std::vector<Node>& trules)
{
  SygusGrammar g = mkDefaultGrammar(opts, range, bvl, trules);
  return g.resolve(true);
}

SygusGrammar SygusGrammarCons::mkDefaultGrammar(const Options& opts,
                                                const TypeNode& range,
                                                const Node& bvl)
{
  // default, include all variables as terminal rules
  std::vector<Node> trules;
  if (!bvl.isNull())
  {
    Assert(bvl.getKind() == BOUND_VAR_LIST);
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
  std::map<TypeNode, std::vector<Node>>::iterator it;
  SygusGrammar g = mkEmptyGrammar(opts, range, bvl, trules);
  std::map<TypeNode, std::vector<Node>> typeToNtSym = getTypeToNtSymMap(g);

  // get the non-terminal for Booleans
  Node ntSymBool;
  TypeNode btype = nm->booleanType();
  it = typeToNtSym.find(btype);
  if (it != typeToNtSym.end())
  {
    Assert(!it->second.empty());
    ntSymBool = it->second[0];
  }

  // add the terminal rules
  for (const Node& r : trules)
  {
    TypeNode rt = r.getType();
    it = typeToNtSym.find(rt);
    if (it != typeToNtSym.end())
    {
      Assert(!it->second.empty());
      g.addRule(it->second[0], r);
    }
  }
  for (size_t i = 0; i < s_nstages; i++)
  {
    for (const std::pair<const TypeNode, std::vector<Node>>& gr : typeToNtSym)
    {
      Assert(!gr.second.empty());
      // add rules for each type
      addDefaultRulesTo(opts, g, gr.second[0], typeToNtSym, i);
      // add predicates for the type to the Boolean grammar if it exists
      if (i == 0 && !gr.first.isBoolean() && !ntSymBool.isNull())
      {
        addDefaultPredicateRulesTo(
            opts, g, gr.second[0], ntSymBool, typeToNtSym);
      }
    }
  }
  // Remove disjunctive rules (ITE, OR) if specified. This option is set to
  // false internally for abduction queries.
  if (!opts.quantifiers.sygusGrammarUseDisj)
  {
    const std::vector<Node>& ntSyms = g.getNtSyms();
    for (const Node& sym : ntSyms)
    {
      const std::vector<Node>& rules = g.getRulesFor(sym);
      std::vector<Node> toErase;
      for (const Node& r : rules)
      {
        if (r.getKind() == OR || r.getKind() == ITE)
        {
          toErase.push_back(r);
        }
      }
      for (const Node& r : toErase)
      {
        g.removeRule(sym, r);
      }
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
    Assert(bvl.getKind() == BOUND_VAR_LIST);
    vars.insert(vars.end(), bvl.begin(), bvl.end());
  }
  // collect the types we are considering, which is all component types of
  // the range type and the initial terminal rules. We also always include
  // Bool.
  std::unordered_set<TypeNode> types;
  for (const Node& r : trules)
  {
    // constants don't contribute anything by themselves
    if (!r.isConst())
    {
      collectTypes(r.getType(), types);
    }
  }
  collectTypes(range, types);
  // always include Boolean
  TypeNode btype = nm->booleanType();
  types.insert(btype);
  // the range type comes first
  std::vector<TypeNode> tvec;
  tvec.push_back(range);
  Trace("sygus-grammar-def")
      << "For " << range << ", trules=" << trules << ", consider types";
  for (const TypeNode& t : types)
  {
    Trace("sygus-grammar-def") << " " << t;
    if (t != range)
    {
      tvec.push_back(t);
    }
  }
  Trace("sygus-grammar-def") << std::endl;

  // construct the non-terminals
  std::vector<Node> ntSyms;
  options::SygusGrammarConsMode tsgcm = opts.quantifiers.sygusGrammarConsMode;
  for (const TypeNode& t : tvec)
  {
    std::stringstream ss;
    ss << "A_";
    if (t.getNumChildren() > 0)
    {
      ss << t.getKind() << "_" << t.getId();
    }
    else
    {
      ss << t;
    }
    Node a = nm->mkBoundVar(ss.str(), t);
    ntSyms.push_back(a);
    // Some types require more than one non-terminal. Handle these cases here.
    if (t.isReal())
    {
      // the positive real constant grammar, for denominators
      Node apc = nm->mkBoundVar("A_Real_PosC", t);
      ntSyms.push_back(apc);
    }
    if (tsgcm == options::SygusGrammarConsMode::ANY_TERM
        || tsgcm == options::SygusGrammarConsMode::ANY_TERM_CONCISE)
    {
      if (t.isRealOrInt())
      {
        // construction of the any-term grammar requires an auxiliary
        // "any constant".
        std::stringstream ssc;
        ssc << "A_" << t << "_AnyC";
        Node aac = nm->mkBoundVar(ssc.str(), t);
        ntSyms.push_back(aac);
      }
    }
  }

  // contruct the grammar
  SygusGrammar ret(vars, ntSyms);
  return ret;
}

void SygusGrammarCons::addDefaultRulesTo(
    const Options& opts,
    SygusGrammar& g,
    const Node& ntSym,
    const std::map<TypeNode, std::vector<Node>>& typeToNtSym,
    size_t stage)
{
  TypeNode tn = ntSym.getType();
  std::vector<Node> prevRules = g.getRulesFor(ntSym);
  NodeManager* nm = NodeManager::currentNM();
  options::SygusGrammarConsMode tsgcm = opts.quantifiers.sygusGrammarConsMode;
  // add constants
  if (stage == 0)
  {
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
    if (tsgcm == options::SygusGrammarConsMode::ANY_CONST)
    {
      if (tn.isBoolean())
      {
        tsgcm = options::SygusGrammarConsMode::SIMPLE;
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
        // if the constant is not already there
        if (std::find(prevRules.begin(), prevRules.end(), c) == prevRules.end())
        {
          g.addRule(ntSym, c);
        }
      }
    }
    // add the operators
    if (tn.isRealOrInt())
    {
      std::map<TypeNode, std::vector<Node>>::const_iterator it =
          typeToNtSym.find(tn);
      const std::vector<Node>& arithNtSym = it->second;
      // we delay construction until the next phase if considering the any
      // term grammar
      if (tsgcm != options::SygusGrammarConsMode::ANY_TERM
          && tsgcm != options::SygusGrammarConsMode::ANY_TERM_CONCISE)
      {
        std::vector<TypeNode> cargsBin;
        cargsBin.push_back(tn);
        cargsBin.push_back(tn);
        // Add ADD, SUB
        std::vector<Kind> kinds = {ADD, SUB};
        for (Kind kind : kinds)
        {
          Trace("sygus-grammar-def") << "...add for " << kind << std::endl;
          addRuleTo(g, typeToNtSym, kind, cargsBin);
        }
        if (tn.isReal())
        {
          // in case of mixed arithmetic, include conversion TO_REAL
          /*
          TypeNode itype = nm->integerType();
          std::vector<TypeNode> cargsToReal;
          cargsToReal.push_back(itype);
          addRuleTo(g, typeToNtSym, TO_REAL, cargsToReal);
          */
          Trace("sygus-grammar-def") << "...add for DIVISION" << std::endl;
          Assert(arithNtSym.size() >= 2);
          // add rule for constant division
          Node ntSymPosC = arithNtSym[1];
          Node divRule = nm->mkNode(DIVISION, ntSym, ntSymPosC);
          g.addRule(ntSym, divRule);
        }
      }
      if (tn.isReal())
      {
        Assert(arithNtSym.size() >= 2);
        Node ntSymPosC = arithNtSym[1];
        // add the rules for positive constants
        Node one = nm->mkConstReal(Rational(1));
        g.addRule(ntSymPosC, one);
        Node rulePlusOne = nm->mkNode(ADD, ntSymPosC, one);
        g.addRule(ntSymPosC, rulePlusOne);
      }
    }
    else if (tn.isBitVector())
    {
      // unary ops
      std::vector<Kind> un_kinds = {BITVECTOR_NOT, BITVECTOR_NEG};
      std::vector<TypeNode> cargsUnary;
      cargsUnary.push_back(tn);
      for (Kind kind : un_kinds)
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
      for (Kind kind : bin_kinds)
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
      for (Kind kind : unary_kinds)
      {
        Trace("sygus-grammar-def") << "...add for " << kind << std::endl;
        addRuleTo(g, typeToNtSym, kind, cargs);
      }
      // binary ops
      {
        Kind kind = FLOATINGPOINT_REM;
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
      std::vector<TypeNode> cargs_rm = {rmType, tn};
      for (Kind kind : binary_rm_kinds)
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
      for (Kind kind : ternary_rm_kinds)
      {
        Trace("sygus-grammar-def") << "...add for " << kind << std::endl;
        addRuleTo(g, typeToNtSym, kind, cargs_rm);
      }
      // quaternary ops
      {
        cargs_rm.push_back(tn);
        Kind kind = FLOATINGPOINT_FMA;
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
      Trace("sygus-grammar-def") << "...building for array type " << tn << "\n";
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
      Trace("sygus-grammar-def")
          << "...add select for constituent type" << elemType << "\n";
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
      for (Kind kind : bin_kinds)
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
          cargsCons.push_back(tsargs[j]);
          // add to the selector type the selector operator
          std::vector<TypeNode> cargsSel;
          cargsSel.push_back(tn);
          Trace("sygus-grammar-def") << "...for " << dt[l][j].getName()
                                     << ", args = " << tn << std::endl;
          Node sel = dt[l][j].getSelector();
          addRuleTo(g, typeToNtSym, APPLY_SELECTOR, sel, cargsSel);
        }
        addRuleTo(g, typeToNtSym, APPLY_CONSTRUCTOR, cop, cargsCons);
      }
    }
    else if (tn.isFunction())
    {
      std::vector<TypeNode> cargs = tn.getArgTypes();
      // add APPLY_UF for the previous rules added (i.e. the function variables)
      for (const Node& r : prevRules)
      {
        addRuleTo(g, typeToNtSym, APPLY_UF, r, cargs);
      }
    }
    else if (tn.isUninterpretedSort() || tn.isRoundingMode() || tn.isBoolean())
    {
      // do nothing
    }
    else
    {
      Warning()
          << "Warning: No implementation for default Sygus grammar of type "
          << tn << std::endl;
    }
  }
  else if (stage == 1)
  {
    // add the operators
    if (tn.isRealOrInt())
    {
      std::map<TypeNode, std::vector<Node>>::const_iterator it =
          typeToNtSym.find(tn);
      const std::vector<Node>& arithNtSym = it->second;
      std::vector<TypeNode> cargsBin;
      cargsBin.push_back(tn);
      cargsBin.push_back(tn);

      if (tsgcm == options::SygusGrammarConsMode::ANY_TERM
          || tsgcm == options::SygusGrammarConsMode::ANY_TERM_CONCISE)
      {
        // whether we will use the polynomial grammar
        bool polynomialGrammar =
            tsgcm == options::SygusGrammarConsMode::ANY_TERM_CONCISE;
        // We have initialized the given type sdts[i], which should now contain
        // a constructor for each relevant arithmetic term/variable. We now
        // construct a sygus datatype of one of the following two forms.
        //
        // (1) The "sum of monomials" grammar:
        //   I -> C*x1 | ... | C*xn | C | I + I | ite( B, I, I )
        //   C -> any_constant
        // where x1, ..., xn are the arithmetic terms/variables (non-arithmetic
        // builtin operators) terms we have considered thus far.
        //
        // (2) The "polynomial" grammar:
        //   I -> C*x1 + ... + C*xn + C | ite( B, I, I )
        //   C -> any_constant
        //
        // The advantage of the first is that it allows for sums of terms
        // constructible from other theories that share sorts with arithmetic,
        // e.g.
        //   c1*str.len(x) + c2*str.len(y)
        // The advantage of the second is that there are fewer constructors, and
        // hence may be more efficient.
        Node ntSymAnyC = arithNtSym.back();
        std::vector<Node> mons;
        for (const Node& r : prevRules)
        {
          if (r.isConst())
          {
            continue;
          }
          // don't use polynomial grammar if there is a term with arguments
          if (r.getNumChildren() > 0)
          {
            polynomialGrammar = false;
          }
          // make the monomial
          Node mon = nm->mkNode(MULT, ntSymAnyC, r);
          mons.push_back(mon);
        }
        mons.push_back(ntSymAnyC);
        // clear the rules
        for (const Node& r : prevRules)
        {
          g.removeRule(ntSym, r);
        }
        // if polynomail grammar
        if (polynomialGrammar)
        {
          // add single rule for the sum
          Node sum = mons.size() == 1 ? mons[0] : nm->mkNode(ADD, mons);
          g.addRule(ntSym, sum);
        }
        else
        {
          // add each monomial as a rule
          for (const Node& m : mons)
          {
            if (m == ntSymAnyC)
            {
              g.addAnyConstant(ntSym, tn);
            }
            else
            {
              g.addRule(ntSym, m);
            }
          }
          addRuleTo(g, typeToNtSym, ADD, cargsBin);
        }
        // initialize the any-constant grammar
        Assert(arithNtSym.size() >= 2);
        g.addAnyConstant(ntSymAnyC, tn);
      }
    }
    else if (tn.isBoolean())
    {
      // only add connectives if non-trivial
      bool triv = true;
      for (const Node& r : prevRules)
      {
        if (!r.isConst())
        {
          triv = false;
          break;
        }
      }
      // if trivial, don't add any further constructors
      if (triv)
      {
        return;
      }
      std::vector<Kind> kinds = {NOT, AND, OR};
      for (Kind k : kinds)
      {
        Trace("sygus-grammar-def") << "...add for " << k << std::endl;
        std::vector<TypeNode> cargs;
        cargs.push_back(tn);
        if (k != NOT)
        {
          cargs.push_back(tn);
        }
        addRuleTo(g, typeToNtSym, k, cargs);
      }
    }

    if (g.getRulesFor(ntSym).empty())
    {
      // if there are not constructors yet by this point, which can happen,
      // e.g. for unimplemented types that have no variables in the argument
      // list of the function-to-synthesize, create a fresh ground term
      g.addRule(ntSym, nm->mkGroundTerm(tn));
    }
    // now, ITE which always comes last
    bool considerIte = true;
    if (tn.isBoolean())
    {
      // don't consider ITE for Booleans, unless unif-pi is enabled (to allow
      // decision tree learning) and the grammar is non-trivial.
      considerIte = false;
      if (!prevRules.empty()
          && opts.quantifiers.sygusUnifPi != options::SygusUnifPiMode::NONE)
      {
        considerIte = true;
      }
    }
    if (considerIte)
    {
      TypeNode btype = nm->booleanType();
      Kind k = ITE;
      Trace("sygus-grammar-def") << "...add for " << k << std::endl;
      std::vector<TypeNode> cargsIte;
      cargsIte.push_back(btype);
      cargsIte.push_back(tn);
      cargsIte.push_back(tn);
      addRuleTo(g, typeToNtSym, ITE, cargsIte);
    }
  }
}

void SygusGrammarCons::collectTypes(const TypeNode& range,
                                    std::unordered_set<TypeNode>& types)
{
  NodeManager* nm = NodeManager::currentNM();
  if (types.find(range) != types.end())
  {
    return;
  }
  if (range.isDatatype())
  {
    // special case: datatypes we add itself and its subfield types, taking
    // into account parametric datatypes
    types.insert(range);
    const DType& dt = range.getDType();
    for (size_t i = 0, size = dt.getNumConstructors(); i < size; ++i)
    {
      // get the specialized constructor type, which accounts for
      // parametric datatypes
      TypeNode ctn = dt[i].getInstantiatedConstructorType(range);
      std::vector<TypeNode> argTypes = ctn.getArgTypes();
      for (size_t j = 0, nargs = argTypes.size(); j < nargs; ++j)
      {
        collectTypes(argTypes[j], types);
      }
    }
    return;
  }
  else if (range.isUninterpretedSort())
  {
    // special case: uninterpreted sorts (which include sorts constructed
    // from uninterpreted sort constructors), we only add the sort itself.
    types.insert(range);
    return;
  }
  // otherwise, get the component types
  expr::getComponentTypes(range, types);
  // add further types based on theory symbols
  if (range.isStringLike())
  {
    // theory of strings shares the integer type, e.g. for length
    TypeNode intType = nm->integerType();
    types.insert(intType);
  }
  else if (range.isFloatingPoint())
  {
    // FP also includes RoundingMode type
    TypeNode rmType = nm->roundingModeType();
    types.insert(rmType);
  }
}

void SygusGrammarCons::addDefaultPredicateRulesTo(
    const Options& opts,
    SygusGrammar& g,
    const Node& ntSym,
    const Node& ntSymBool,
    const std::map<TypeNode, std::vector<Node>>& typeToNtSym)
{
  NodeManager* nm = NodeManager::currentNM();
  Assert(!ntSym.getType().isBoolean());
  Assert(ntSymBool.getType().isBoolean());
  TypeNode tn = ntSym.getType();

  std::vector<TypeNode> cargsBin;
  cargsBin.push_back(tn);
  cargsBin.push_back(tn);

  bool realIntZeroArg = false;
  if (tn.isRealOrInt())
  {
    realIntZeroArg = (opts.quantifiers.sygusGrammarConsMode
                      == options::SygusGrammarConsMode::ANY_TERM_CONCISE);
  }

  // add equality per type, if first class
  if (tn.isFirstClass())
  {
    Trace("sygus-grammar-def") << "...add for EQUAL" << std::endl;
    if (realIntZeroArg)
    {
      // optimization: consider (= x 0)
      Node rule =
          nm->mkNode(EQUAL, ntSym, nm->mkConstRealOrInt(tn, Rational(0)));
      g.addRule(ntSymBool, rule);
    }
    else
    {
      addRuleTo(g, typeToNtSym, EQUAL, cargsBin);
    }
  }

  // type specific predicates
  if (tn.isRealOrInt())
  {
    Trace("sygus-grammar-def") << "...add for LEQ" << std::endl;
    if (realIntZeroArg)
    {
      // optimization: consider (<= 0 ntSym)
      Node rule = nm->mkNode(LEQ, nm->mkConstRealOrInt(tn, Rational(0)), ntSym);
      g.addRule(ntSymBool, rule);
    }
    else
    {
      addRuleTo(g, typeToNtSym, LEQ, cargsBin);
    }
  }
  else if (tn.isBitVector())
  {
    Trace("sygus-grammar-def") << "...add for BV" << std::endl;
    addRuleTo(g, typeToNtSym, BITVECTOR_ULT, cargsBin);
  }
  else if (tn.isFloatingPoint())
  {
    Trace("sygus-grammar-def") << "...add FP predicates" << std::endl;
    std::vector<Kind> fp_unary_predicates = {FLOATINGPOINT_IS_NORMAL,
                                             FLOATINGPOINT_IS_SUBNORMAL,
                                             FLOATINGPOINT_IS_ZERO,
                                             FLOATINGPOINT_IS_INF,
                                             FLOATINGPOINT_IS_NAN,
                                             FLOATINGPOINT_IS_NEG,
                                             FLOATINGPOINT_IS_POS};
    std::vector<TypeNode> cargsUn;
    cargsUn.push_back(tn);
    for (Kind kind : fp_unary_predicates)
    {
      addRuleTo(g, typeToNtSym, kind, cargsUn);
    }
    std::vector<Kind> fp_binary_predicates = {FLOATINGPOINT_LEQ,
                                              FLOATINGPOINT_LT};
    for (Kind kind : fp_binary_predicates)
    {
      addRuleTo(g, typeToNtSym, kind, cargsBin);
    }
  }
  else if (tn.isDatatype())
  {
    // add for testers
    Trace("sygus-grammar-def") << "...add for testers" << std::endl;
    const DType& dt = tn.getDType();
    std::vector<TypeNode> cargsTester;
    cargsTester.push_back(tn);
    for (unsigned kind = 0, size_k = dt.getNumConstructors(); kind < size_k;
         ++kind)
    {
      Trace("sygus-grammar-def")
          << "...for " << dt[kind].getTester() << std::endl;
      Node t = dt[kind].getTester();
      addRuleTo(g, typeToNtSym, APPLY_TESTER, t, cargsTester);
    }
  }
  else if (tn.isSet())
  {
    // add for member
    TypeNode etype = tn.getSetElementType();
    std::vector<TypeNode> cargsMember;
    cargsMember.push_back(etype);
    cargsMember.push_back(tn);
    Trace("sygus-grammar-def") << "...for SET_MEMBER" << std::endl;
    addRuleTo(g, typeToNtSym, SET_MEMBER, cargsMember);
  }
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

std::map<TypeNode, std::vector<Node>> SygusGrammarCons::getTypeToNtSymMap(
    const SygusGrammar& g)
{
  std::map<TypeNode, std::vector<Node>> typeToNtSym;
  const std::vector<Node>& ntSyms = g.getNtSyms();
  for (const Node& s : ntSyms)
  {
    TypeNode stn = s.getType();
    typeToNtSym[stn].push_back(s);
  }
  return typeToNtSym;
}

bool SygusGrammarCons::addRuleTo(
    SygusGrammar& g,
    const std::map<TypeNode, std::vector<Node>>& typeToNtSym,
    Kind k,
    const std::vector<TypeNode>& args)
{
  Node op;
  return addRuleTo(g, typeToNtSym, k, op, args);
}

bool SygusGrammarCons::addRuleTo(
    SygusGrammar& g,
    const std::map<TypeNode, std::vector<Node>>& typeToNtSym,
    Kind k,
    const Node& op,
    const std::vector<TypeNode>& args)
{
  std::map<TypeNode, std::vector<Node>>::const_iterator it;
  std::vector<Node> children;
  if (!op.isNull())
  {
    children.push_back(op);
  }
  for (const TypeNode& a : args)
  {
    it = typeToNtSym.find(a);
    if (it == typeToNtSym.end())
    {
      return false;
    }
    Assert(!it->second.empty());
    children.push_back(it->second[0]);
  }
  Node rule = NodeManager::currentNM()->mkNode(k, children);
  TypeNode rtn = rule.getType();
  it = typeToNtSym.find(rtn);
  if (it == typeToNtSym.end())
  {
    return false;
  }
  Assert(!it->second.empty());
  g.addRule(it->second[0], rule);
  return true;
}

}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal
