/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Francois Bobot, Haniel Barbosa
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2022 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Definition of TPTP parser.
 */

// Do not #include "parser/antlr_input.h" directly. Rely on the header.
#include "parser/tptp/tptp.h"

#include <algorithm>
#include <set>

#include "api/cpp/cvc5.h"
#include "base/check.h"
#include "parser/api/cpp/command.h"
#include "parser/parser.h"
#include "theory/logic_info.h"

// ANTLR defines these, which is really bad!
#undef true
#undef false

namespace cvc5 {
namespace parser {

Tptp::Tptp(cvc5::Solver* solver,
           SymbolManager* sm,
           bool strictMode,
           bool parseOnly)
    : Parser(solver, sm, strictMode, parseOnly),
      d_cnf(false),
      d_fof(false),
      d_hol(false)
{
  addTheory(Tptp::THEORY_CORE);

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
    preemptCommand(new SetBenchmarkLogicCommand(sm->getForcedLogic()));
  }
}

Tptp::~Tptp() {
  for( unsigned i=0; i<d_in_created.size(); i++ ){
    d_in_created[i]->free(d_in_created[i]);
  }
}

void Tptp::addTheory(Theory theory) {
  switch(theory) {
  case THEORY_CORE:
    //TPTP (CNF and FOF) is unsorted so we define this common type
    {
      std::string d_unsorted_name = "$$unsorted";
      d_unsorted = d_solver->mkUninterpretedSort(d_unsorted_name);
      preemptCommand(new DeclareSortCommand(d_unsorted_name, 0, d_unsorted));
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
    ss << "internal error: Tptp::addTheory(): unhandled theory " << theory;
    throw ParserException(ss.str());
  }
}


/* The include are managed in the lexer but called in the parser */
// Inspired by http://www.antlr3.org/api/C/interop.html

bool newInputStream(std::string fileName, pANTLR3_LEXER lexer, std::vector< pANTLR3_INPUT_STREAM >& inc ) {
  Trace("parser") << "Including " << fileName << std::endl;
  // Create a new input stream and take advantage of built in stream stacking
  // in C target runtime.
  //
  pANTLR3_INPUT_STREAM    in;
#ifdef CVC5_ANTLR3_OLD_INPUT_STREAM
  in = antlr3AsciiFileStreamNew((pANTLR3_UINT8) fileName.c_str());
#else  /* CVC5_ANTLR3_OLD_INPUT_STREAM */
  in = antlr3FileStreamNew((pANTLR3_UINT8) fileName.c_str(), ANTLR3_ENC_8BIT);
#endif /* CVC5_ANTLR3_OLD_INPUT_STREAM */
  if(in == NULL) {
    Trace("parser") << "Can't open " << fileName << std::endl;
    return false;
  }
  // Same thing as the predefined PUSHSTREAM(in);
  lexer->pushCharStream(lexer,in);
  // restart it
  //lexer->rec->state->tokenStartCharIndex  = -10;
  //lexer->emit(lexer);

  // Note that the input stream is not closed when it EOFs, I don't bother
  // to do it here, but it is up to you to track streams created like this
  // and destroy them when the whole parse session is complete. Remember that you
  // don't want to do this until all tokens have been manipulated all the way through
  // your tree parsers etc as the token does not store the text it just refers
  // back to the input stream and trying to get the text for it will abort if you
  // close the input stream too early.
  //
  inc.push_back( in );

  //TODO what said before
  return true;
}

void Tptp::includeFile(std::string fileName) {
  // security for online version
  if(!canIncludeFile()) {
    parseError("include-file feature was disabled for this run.");
  }

  // Get the lexer
  AntlrInput * ai = static_cast<AntlrInput *>(getInput());
  pANTLR3_LEXER lexer = ai->getAntlr3Lexer();

  // push the inclusion scope; will be popped by our special popCharStream
  // would be necessary for handling symbol filtering in inclusions
  //pushScope();

  // get the name of the current stream "Does it work inside an include?"
  const std::string inputName = ai->getInputStreamName();

  // Test in the directory of the actual parsed file
  std::string currentDirFileName;
  if(inputName != "<stdin>") {
    // TODO: Use dirname or Boost::filesystem?
    size_t pos = inputName.rfind('/');
    if(pos != std::string::npos) {
      currentDirFileName = std::string(inputName, 0, pos + 1);
    }
    currentDirFileName.append(fileName);
    if(newInputStream(currentDirFileName,lexer, d_in_created)) {
      return;
    }
  } else {
    currentDirFileName = "<unknown current directory for stdin>";
  }

  if(d_tptpDir.empty()) {
    parseError("Couldn't open included file: " + fileName
               + " at " + currentDirFileName + " and the TPTP directory is not specified (environment variable TPTP)");
  };

  std::string tptpDirFileName = d_tptpDir + fileName;
  if(! newInputStream(tptpDirFileName,lexer, d_in_created)) {
    parseError("Couldn't open included file: " + fileName
               + " at " + currentDirFileName + " or " + tptpDirFileName);
  }
}

void Tptp::checkLetBinding(const std::vector<cvc5::Term>& bvlist,
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

cvc5::Term Tptp::parseOpToExpr(ParseOp& p)
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
    cvc5::Sort t =
        p.d_type == d_solver->getBooleanSort() ? p.d_type : d_unsorted;
    expr = bindVar(p.d_name, t);  // must define at level zero
    d_auxSymbolTable[p.d_name] = expr;
    preemptCommand(new DeclareFunctionCommand(p.d_name, expr, t));
  }
  return expr;
}

cvc5::Term Tptp::isTptpDeclared(const std::string& name)
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

Term Tptp::makeApplyUf(std::vector<Term>& args)
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
  return d_solver->mkTerm(APPLY_UF, args);
}

cvc5::Term Tptp::applyParseOp(ParseOp& p, std::vector<cvc5::Term>& args)
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
  if (p.d_kind == cvc5::NULL_TERM)
  {
    // A non-built-in function application, get the expression
    cvc5::Term v = isTptpDeclared(p.d_name);
    if (v.isNull())
    {
      std::vector<cvc5::Sort> sorts(args.size(), d_unsorted);
      cvc5::Sort t =
          p.d_type == d_solver->getBooleanSort() ? p.d_type : d_unsorted;
      t = d_solver->mkFunctionSort(sorts, t);
      v = bindVar(p.d_name, t);  // must define at level zero
      d_auxSymbolTable[p.d_name] = v;
      preemptCommand(new DeclareFunctionCommand(p.d_name, v, t));
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

cvc5::Term Tptp::mkDecimal(
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

bool Tptp::hol() const { return d_hol; }
void Tptp::setHol()
{
  if (d_hol)
  {
    return;
  }
  d_hol = true;
  d_solver->setLogic("HO_UF");
}

void Tptp::addFreeVar(cvc5::Term var)
{
  Assert(cnf());
  d_freeVar.push_back(var);
}

std::vector<cvc5::Term> Tptp::getFreeVar()
{
  Assert(cnf());
  std::vector<cvc5::Term> r;
  r.swap(d_freeVar);
  return r;
}

cvc5::Term Tptp::convertRatToUnsorted(cvc5::Term expr)
{
  // Create the conversion function If they doesn't exists
  if (d_rtu_op.isNull()) {
    cvc5::Sort t;
    // Conversion from rational to unsorted
    t = d_solver->mkFunctionSort({d_solver->getRealSort()}, d_unsorted);
    d_rtu_op = d_solver->mkConst(t, "$$rtu");
    preemptCommand(new DeclareFunctionCommand("$$rtu", d_rtu_op, t));
    // Conversion from unsorted to rational
    t = d_solver->mkFunctionSort({d_unsorted}, d_solver->getRealSort());
    d_utr_op = d_solver->mkConst(t, "$$utr");
    preemptCommand(new DeclareFunctionCommand("$$utr", d_utr_op, t));
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
    preemptCommand(new AssertCommand(eq));
  }
  return cvc5::Term(ret);
}

cvc5::Term Tptp::convertStrToUnsorted(std::string str)
{
  cvc5::Term& e = d_distinct_objects[str];
  if (e.isNull())
  {
    e = d_solver->mkConst(d_unsorted, str);
  }
  return e;
}

cvc5::Term Tptp::mkLambdaWrapper(cvc5::Kind k, cvc5::Sort argType)
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

cvc5::Term Tptp::getAssertionExpr(FormulaRole fr, cvc5::Term expr)
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

cvc5::Term Tptp::getAssertionDistinctConstants()
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

Command* Tptp::makeAssertCommand(FormulaRole fr, cvc5::Term expr, bool cnf)
{
  // For SZS ontology compliance.
  // if we're in cnf() though, conjectures don't result in "Theorem" or
  // "CounterSatisfiable".
  if (!cnf && (fr == FR_NEGATED_CONJECTURE || fr == FR_CONJECTURE)) {
    d_hasConjecture = true;
    Assert(!expr.isNull());
  }
  if( expr.isNull() ){
    return new EmptyCommand("Untreated role for expression");
  }else{
    return new AssertCommand(expr);
  }
}

}  // namespace parser
}  // namespace cvc5
