/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Haniel Barbosa, Francois Bobot
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Definition of TPTP parser.
 */

// Do not #include "parser/antlr_input.h" directly. Rely on the header.
#include "parser/tptp/tptp.h"

#include <cvc5/cvc5.h>

#include <algorithm>
#include <set>

#include "base/check.h"
#include "parser/api/cpp/command.h"
#include "parser/parser.h"
#include "theory/logic_info.h"

namespace cvc5 {
namespace parser {

TptpState::TptpState(ParserStateCallback* psc,
                     Solver* solver,
                     SymbolManager* sm,
                     bool strictMode)
    : ParserState(psc, solver, sm, strictMode),
      d_cnf(false),
      d_fof(false),
      d_hol(false)
{
  // To ensure there are no conflicts with smt2 builtin symbols, we use a
  // print namespace. This ensures that benchmarks coverted TPTP to smt2
  // can be reparsed with -o raw-benchmark.
  d_printNamespace = "tptp.";
  addTheory(TptpState::THEORY_CORE);

  /* Try to find TPTP dir */
  // From tptp4x FileUtilities
  //----Try the TPTP directory, and TPTP variations
  char* home = getenv("TPTP");
  if(home == NULL) {
     home = getenv("TPTP_HOME");
// //----If no TPTP_HOME, try the tptp user (aaargh)
//         if(home == NULL && (PasswdEntry = getpwnam("tptp")) != NULL) {
//            home = PasswdEntry->pw_dir;
//         }
//----Now look in the TPTP directory from there
    if(home != NULL) {
      d_tptpDir = home;
      d_tptpDir.append("/TPTP/");
    }
  } else {
    d_tptpDir = home;
    //add trailing "/"
    if(d_tptpDir[d_tptpDir.size() - 1] != '/') {
      d_tptpDir.append("/");
    }
  }
  d_hasConjecture = false;
  // Handle forced logic immediately.
  if (sm->isLogicForced())
  {
    preemptCommand(std::make_unique<SetBenchmarkLogicCommand>(sm->getLogic()));
  }
}

TptpState::~TptpState() {}

void TptpState::addTheory(Theory theory)
{
  switch(theory) {
  case THEORY_CORE:
    //TPTP (CNF and FOF) is unsorted so we define this common type
    {
      std::string d_unsorted_name = "$$unsorted";
      d_unsorted = d_solver->mkUninterpretedSort(d_unsorted_name);
      preemptCommand(
          std::make_unique<DeclareSortCommand>(d_unsorted_name, 0, d_unsorted));
    }
    // propositionnal
    defineType("Bool", d_solver->getBooleanSort());
    defineVar("$true", d_solver->mkTrue());
    defineVar("$false", d_solver->mkFalse());
    addOperator(cvc5::AND);
    addOperator(cvc5::EQUAL);
    addOperator(cvc5::IMPLIES);
    // addOperator(cvc5::ITE); //only for tff thf
    addOperator(cvc5::NOT);
    addOperator(cvc5::OR);
    addOperator(cvc5::XOR);
    addOperator(cvc5::APPLY_UF);
    //Add quantifiers?
    break;

  default:
    std::stringstream ss;
    ss << "internal error: TptpState::addTheory(): unhandled theory " << theory;
    throw ParserException(ss.str());
  }
}

void TptpState::checkLetBinding(const std::vector<cvc5::Term>& bvlist,
                                cvc5::Term lhs,
                                cvc5::Term rhs,
                                bool formula)
{
  if (lhs.getKind() != cvc5::APPLY_UF)
  {
    parseError("malformed let: LHS must be a flat function application");
  }
  const std::multiset<cvc5::Term> vars{lhs.begin(), lhs.end()};
  if (formula && !lhs.getSort().isBoolean())
  {
    parseError("malformed let: LHS must be formula");
  }
  for (const cvc5::Term& var : vars)
  {
    if (var.hasOp())
    {
      parseError("malformed let: LHS must be flat, illegal child: " +
                 var.toString());
    }
  }

  // ensure all let-bound variables appear on the LHS, and appear only once
  for (const cvc5::Term& bound_var : bvlist)
  {
    const size_t count = vars.count(bound_var);
    if (count == 0) {
      parseError(
          "malformed let: LHS must make use of all quantified variables, "
          "missing `" +
          bound_var.toString() + "'");
    } else if (count >= 2) {
      parseError("malformed let: LHS cannot use same bound variable twice: " +
                 bound_var.toString());
    }
  }
}

cvc5::Term TptpState::parseOpToExpr(ParseOp& p)
{
  cvc5::Term expr;
  if (!p.d_expr.isNull())
  {
    return p.d_expr;
  }
  // if it has a kind, it's a builtin one and this function should not have been
  // called
  Assert(p.d_kind == cvc5::NULL_TERM);
  expr = isTptpDeclared(p.d_name);
  if (expr.isNull())
  {
    cvc5::Sort t = isPredicate(p) ? d_solver->getBooleanSort() : d_unsorted;
    expr = bindVar(p.d_name, t);  // must define at level zero
    d_auxSymbolTable[p.d_name] = expr;
    preemptCommand(std::make_unique<DeclareFunctionCommand>(p.d_name, expr, t));
  }
  return expr;
}

cvc5::Term TptpState::isTptpDeclared(const std::string& name)
{
  if (isDeclared(name))
  {  // already appeared
    return getVariable(name);
  }
  std::unordered_map<std::string, cvc5::Term>::iterator it =
      d_auxSymbolTable.find(name);
  if (it != d_auxSymbolTable.end())
  {
    return it->second;
  }
  // otherwise null
  return cvc5::Term();
}

Term TptpState::makeApplyUf(std::vector<Term>& args)
{
  std::vector<Sort> argSorts = args[0].getSort().getFunctionDomainSorts();
  if (argSorts.size() + 1 != args.size())
  {
    // arity mismatch
    parseError("Applying function to wrong number of arguments");
  }
  for (size_t i = 0, nargs = argSorts.size(); i < nargs; i++)
  {
    if (argSorts[i].isReal() && args[i + 1].getSort().isInteger())
    {
      args[i + 1] = d_solver->mkTerm(TO_REAL, {args[i + 1]});
    }
  }
  // If a lambda, apply it immediately. This is furthermore important to
  // avoid lambdas with `-o raw-benchmark` when higher-order is not enabled.
  if (args[0].getKind() == LAMBDA)
  {
    std::vector<Term> vars(args[0][0].begin(), args[0][0].end());
    std::vector<Term> subs(args.begin() + 1, args.end());
    return args[0][1].substitute(vars, subs);
  }

  return d_solver->mkTerm(APPLY_UF, args);
}

cvc5::Term TptpState::applyParseOp(ParseOp& p, std::vector<cvc5::Term>& args)
{
  if (TraceIsOn("parser"))
  {
    Trace("parser") << "applyParseOp: " << p << " to:" << std::endl;
    for (std::vector<cvc5::Term>::iterator i = args.begin(); i != args.end();
         ++i)
    {
      Trace("parser") << "++ " << *i << std::endl;
    }
  }
  Assert(!args.empty());
  // If operator already defined, just build application
  if (!p.d_expr.isNull())
  {
    // this happens with some arithmetic kinds, which are wrapped around
    // lambdas.
    args.insert(args.begin(), p.d_expr);
    return makeApplyUf(args);
  }
  bool isBuiltinKind = false;
  // the builtin kind of the overall return expression
  cvc5::Kind kind = cvc5::NULL_TERM;
  // First phase: piece operator together
  if (p.d_kind == cvc5::NULL_TERM || p.d_kind == cvc5::CONST_BOOLEAN)
  {
    // A non-built-in function application, get the expression
    cvc5::Term v = isTptpDeclared(p.d_name);
    if (v.isNull())
    {
      std::vector<cvc5::Sort> sorts(args.size(), d_unsorted);
      cvc5::Sort t = isPredicate(p) ? d_solver->getBooleanSort() : d_unsorted;
      t = d_solver->mkFunctionSort(sorts, t);
      v = bindVar(p.d_name, t);  // must define at level zero
      d_auxSymbolTable[p.d_name] = v;
      preemptCommand(std::make_unique<DeclareFunctionCommand>(p.d_name, v, t));
    }
    // args might be rationals, in which case we need to create
    // distinct constants of the "unsorted" sort to represent them
    for (size_t i = 0; i < args.size(); ++i)
    {
      if (args[i].getSort().isReal()
          && v.getSort().getFunctionDomainSorts()[i] == d_unsorted)
      {
        args[i] = convertRatToUnsorted(args[i]);
      }
    }
    Assert(!v.isNull());
    checkFunctionLike(v);
    kind = getKindForFunction(v);
    args.insert(args.begin(), v);
  }
  else
  {
    kind = p.d_kind;
    isBuiltinKind = true;
  }
  Assert(kind != cvc5::NULL_TERM);
  // Second phase: apply parse op to the arguments
  if (isBuiltinKind)
  {
    if (kind == cvc5::EQUAL || kind == cvc5::DISTINCT)
    {
      std::vector<Sort> sorts;
      size_t nargs = args.size();
      for (size_t i = 0; i < nargs; i++)
      {
        Sort s = args[i].getSort();
        if (s.isFunction())
        {
          // need hol if these operators are applied over function args
          if (!hol())
          {
            parseError("Cannot apply equalty to functions unless THF.");
          }
        }
        sorts.push_back(s);
      }
      // TPTP assumes Int/Real subtyping, but the cvc5 API does not
      for (size_t i = 0; i < nargs; i++)
      {
        if (sorts[i].isReal())
        {
          // cast all Integer arguments to Real
          for (size_t j = 0; j < nargs; j++)
          {
            if (j != i && sorts[j].isInteger())
            {
              args[j] = d_solver->mkTerm(TO_REAL, {args[j]});
            }
          }
          break;
        }
      }
    }
    if (!strictModeEnabled() && (kind == cvc5::AND || kind == cvc5::OR)
        && args.size() == 1)
    {
      // Unary AND/OR can be replaced with the argument.
      return args[0];
    }
    if (kind == cvc5::SUB && args.size() == 1)
    {
      return d_solver->mkTerm(cvc5::NEG, {args[0]});
    }
    if (kind == cvc5::TO_REAL)
    {
      // If the type is real, this is a no-op. We require this special
      // case in the TPTP parser since TO_REAL is designed to match the
      // SMT-LIB operator, meaning it can only be applied to integers, whereas
      // the TPTP to_real / to_rat do not have the same semantics.
      cvc5::Sort s = args[0].getSort();
      if (s.isReal())
      {
        return args[0];
      }
    }
    return d_solver->mkTerm(kind, args);
  }

  // check if partially applied function, in this case we use HO_APPLY
  if (args.size() >= 2)
  {
    cvc5::Sort argt = args[0].getSort();
    if (argt.isFunction())
    {
      unsigned arity = argt.getFunctionArity();
      if (args.size() - 1 < arity)
      {
        if (!hol())
        {
          parseError("Cannot partially apply functions unless THF.");
        }
        Trace("parser") << "Partial application of " << args[0];
        Trace("parser") << " : #argTypes = " << arity;
        Trace("parser") << ", #args = " << args.size() - 1 << std::endl;
        // must curry the partial application
        return d_solver->mkTerm(cvc5::HO_APPLY, args);
      }
      else if (kind == APPLY_UF)
      {
        // ensure subtyping is not used
        return makeApplyUf(args);
      }
    }
  }
  return d_solver->mkTerm(kind, args);
}

cvc5::Term TptpState::mkDecimal(
    std::string& snum, std::string& sden, bool pos, size_t exp, bool posE)
{
  // the numerator and the denominator
  std::stringstream ssn;
  std::stringstream ssd;
  if (exp != 0)
  {
    if (posE)
    {
      // see if we need to pad zeros on the end, e.g. 1.2E5 ---> 120000
      if (exp >= sden.size())
      {
        ssn << snum << sden;
        for (size_t i = 0, nzero = (exp - sden.size()); i < nzero; i++)
        {
          ssn << "0";
        }
        ssd << "0";
      }
      else
      {
        ssn << snum << sden.substr(0, exp);
        ssd << sden.substr(exp);
      }
    }
    else
    {
      // see if we need to pad zeros on the beginning, e.g. 1.2E-5 ---> 0.000012
      if (exp >= snum.size())
      {
        ssn << "0";
        for (size_t i = 0, nzero = (exp - snum.size()); i < nzero; i++)
        {
          ssd << "0";
        }
        ssd << snum << sden;
      }
      else
      {
        ssn << snum.substr(0, exp);
        ssd << snum.substr(exp) << sden;
      }
    }
  }
  else
  {
    ssn << snum;
    ssd << sden;
  }
  std::stringstream ss;
  if (!pos)
  {
    ss << "-";
  }
  ss << ssn.str() << "." << ssd.str();
  return d_solver->mkReal(ss.str());
}

const std::string& TptpState::getTptpDir() const { return d_tptpDir; }

void TptpState::markPredicate(ParseOp& p) const
{
  // temporary hack to distinguish certain ParseOp as predicates
  // this will be deleted along with the TPTP parser.
  p.d_indices.push_back(1);
}

bool TptpState::isPredicate(ParseOp& p) const { return !p.d_indices.empty(); }

bool TptpState::hol() const { return d_hol; }
void TptpState::setHol()
{
  if (d_hol)
  {
    return;
  }
  d_hol = true;
  // since we can include arithmetic, just set the logic to include all
  d_solver->setLogic("HO_ALL");
}

void TptpState::addFreeVar(cvc5::Term var)
{
  Assert(cnf());
  d_freeVar.push_back(var);
}

std::vector<cvc5::Term> TptpState::getFreeVar()
{
  Assert(cnf());
  std::vector<cvc5::Term> r;
  r.swap(d_freeVar);
  return r;
}

cvc5::Term TptpState::convertRatToUnsorted(cvc5::Term expr)
{
  // Create the conversion function If they doesn't exists
  if (d_rtu_op.isNull()) {
    cvc5::Sort t;
    // Conversion from rational to unsorted
    t = d_solver->mkFunctionSort({d_solver->getRealSort()}, d_unsorted);
    d_rtu_op = d_solver->mkConst(t, "$$rtu");
    preemptCommand(
        std::make_unique<DeclareFunctionCommand>("$$rtu", d_rtu_op, t));
    // Conversion from unsorted to rational
    t = d_solver->mkFunctionSort({d_unsorted}, d_solver->getRealSort());
    d_utr_op = d_solver->mkConst(t, "$$utr");
    preemptCommand(
        std::make_unique<DeclareFunctionCommand>("$$utr", d_utr_op, t));
  }
  // Add the inverse in order to show that over the elements that
  // appear in the problem there is a bijection between unsorted and
  // rational
  std::vector<Term> args = {d_rtu_op, expr};
  Term ret = makeApplyUf(args);
  if (d_r_converted.find(expr) == d_r_converted.end()) {
    d_r_converted.insert(expr);
    if (expr.getSort().isInteger())
    {
      // ensure the equality below is between reals
      expr = d_solver->mkTerm(TO_REAL, {expr});
    }
    cvc5::Term eq = d_solver->mkTerm(
        cvc5::EQUAL, {expr, d_solver->mkTerm(cvc5::APPLY_UF, {d_utr_op, ret})});
    preemptCommand(std::make_unique<AssertCommand>(eq));
  }
  return cvc5::Term(ret);
}

cvc5::Term TptpState::convertStrToUnsorted(std::string str)
{
  cvc5::Term& e = d_distinct_objects[str];
  if (e.isNull())
  {
    e = d_solver->mkConst(d_unsorted, str);
    preemptCommand(std::make_unique<DeclareFunctionCommand>(str, e, d_unsorted));
  }
  return e;
}

cvc5::Term TptpState::mkLambdaWrapper(cvc5::Kind k, cvc5::Sort argType)
{
  Trace("parser") << "mkLambdaWrapper: kind " << k << " and type " << argType
                  << "\n";
  std::vector<cvc5::Term> lvars;
  std::vector<cvc5::Sort> domainTypes = argType.getFunctionDomainSorts();
  for (unsigned i = 0, size = domainTypes.size(); i < size; ++i)
  {
    // the introduced variable is internal (not parsable)
    std::stringstream ss;
    ss << "_lvar_" << i;
    cvc5::Term v = d_solver->mkVar(domainTypes[i], ss.str());
    lvars.push_back(v);
  }
  // apply body of lambda to variables
  cvc5::Term wrapper =
      d_solver->mkTerm(cvc5::LAMBDA,
                       {d_solver->mkTerm(cvc5::VARIABLE_LIST, lvars),
                        d_solver->mkTerm(k, lvars)});

  return wrapper;
}

cvc5::Term TptpState::getAssertionExpr(FormulaRole fr, cvc5::Term expr)
{
  switch (fr) {
    case FR_AXIOM:
    case FR_HYPOTHESIS:
    case FR_DEFINITION:
    case FR_ASSUMPTION:
    case FR_LEMMA:
    case FR_THEOREM:
    case FR_NEGATED_CONJECTURE:
    case FR_PLAIN:
      // it's a usual assert
      return expr;
    case FR_CONJECTURE:
      // it should be negated when asserted
      return d_solver->mkTerm(cvc5::NOT, {expr});
    case FR_UNKNOWN:
    case FR_FI_DOMAIN:
    case FR_FI_FUNCTORS:
    case FR_FI_PREDICATES:
    case FR_TYPE:
      // it does not correspond to an assertion
      return d_nullExpr;
      break;
  }
  Assert(false);  // unreachable
  return d_nullExpr;
}

cvc5::Term TptpState::getAssertionDistinctConstants()
{
  std::vector<cvc5::Term> constants;
  for (std::pair<const std::string, cvc5::Term>& cs : d_distinct_objects)
  {
    constants.push_back(cs.second);
  }
  if (constants.size() > 1)
  {
    return d_solver->mkTerm(cvc5::DISTINCT, constants);
  }
  return d_nullExpr;
}

std::unique_ptr<Command> TptpState::makeAssertCommand(FormulaRole fr,
                                                      cvc5::Term expr,
                                                      bool cnf)
{
  // For SZS ontology compliance.
  // if we're in cnf() though, conjectures don't result in "Theorem" or
  // "CounterSatisfiable".
  if (!cnf && (fr == FR_NEGATED_CONJECTURE || fr == FR_CONJECTURE)) {
    d_hasConjecture = true;
    Assert(!expr.isNull());
  }
  if( expr.isNull() ){
    return std::make_unique<EmptyCommand>("Untreated role for expression");
  }
  return std::make_unique<AssertCommand>(expr);
}

}  // namespace parser
}  // namespace cvc5
