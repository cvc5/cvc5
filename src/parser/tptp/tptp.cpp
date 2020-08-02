/*********************                                                        */
/*! \file tptp.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Francois Bobot, Haniel Barbosa
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Definitions of TPTP constants.
 **
 ** Definitions of TPTP constants.
 **/

// Do not #include "parser/antlr_input.h" directly. Rely on the header.
#include "parser/tptp/tptp.h"

#include <algorithm>
#include <set>

#include "api/cvc4cpp.h"
#include "expr/type.h"
#include "options/options.h"
#include "parser/parser.h"

// ANTLR defines these, which is really bad!
#undef true
#undef false

namespace CVC4 {
namespace parser {

Tptp::Tptp(api::Solver* solver, Input* input, bool strictMode, bool parseOnly)
    : Parser(solver, input, strictMode, parseOnly), d_cnf(false), d_fof(false)
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
      preemptCommand(
          new DeclareTypeCommand(d_unsorted_name, 0, d_unsorted.getType()));
    }
    // propositionnal
    defineType("Bool", d_solver->getBooleanSort());
    defineVar("$true", d_solver->mkTrue());
    defineVar("$false", d_solver->mkFalse());
    addOperator(api::AND);
    addOperator(api::EQUAL);
    addOperator(api::IMPLIES);
    // addOperator(api::ITE); //only for tff thf
    addOperator(api::NOT);
    addOperator(api::OR);
    addOperator(api::XOR);
    addOperator(api::APPLY_UF);
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
  Debug("parser") << "Including " << fileName << std::endl;
  // Create a new input stream and take advantage of built in stream stacking
  // in C target runtime.
  //
  pANTLR3_INPUT_STREAM    in;
#ifdef CVC4_ANTLR3_OLD_INPUT_STREAM
  in = antlr3AsciiFileStreamNew((pANTLR3_UINT8) fileName.c_str());
#else /* CVC4_ANTLR3_OLD_INPUT_STREAM */
  in = antlr3FileStreamNew((pANTLR3_UINT8) fileName.c_str(), ANTLR3_ENC_8BIT);
#endif /* CVC4_ANTLR3_OLD_INPUT_STREAM */
  if(in == NULL) {
    Debug("parser") << "Can't open " << fileName << std::endl;
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

void Tptp::checkLetBinding(const std::vector<api::Term>& bvlist,
                           api::Term lhs,
                           api::Term rhs,
                           bool formula)
{
  if (lhs.getKind() != api::APPLY_UF)
  {
    parseError("malformed let: LHS must be a flat function application");
  }
  const std::multiset<api::Term> vars{lhs.begin(), lhs.end()};
  if (formula && !lhs.getSort().isBoolean())
  {
    parseError("malformed let: LHS must be formula");
  }
  for (const CVC4::api::Term& var : vars)
  {
    if (var.hasOp())
    {
      parseError("malformed let: LHS must be flat, illegal child: " +
                 var.toString());
    }
  }

  // ensure all let-bound variables appear on the LHS, and appear only once
  for (const api::Term& bound_var : bvlist)
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

api::Term Tptp::parseOpToExpr(ParseOp& p)
{
  api::Term expr;
  if (!p.d_expr.isNull())
  {
    return p.d_expr;
  }
  // if it has a kind, it's a builtin one and this function should not have been
  // called
  assert(p.d_kind == api::NULL_EXPR);
  if (isDeclared(p.d_name))
  {  // already appeared
    expr = getVariable(p.d_name);
  }
  else
  {
    api::Sort t =
        p.d_type == d_solver->getBooleanSort() ? p.d_type : d_unsorted;
    expr = bindVar(p.d_name, t, ExprManager::VAR_FLAG_GLOBAL);  // levelZero
    preemptCommand(
        new DeclareFunctionCommand(p.d_name, expr.getExpr(), t.getType()));
  }
  return expr;
}

api::Term Tptp::applyParseOp(ParseOp& p, std::vector<api::Term>& args)
{
  if (Debug.isOn("parser"))
  {
    Debug("parser") << "applyParseOp: " << p << " to:" << std::endl;
    for (std::vector<api::Term>::iterator i = args.begin(); i != args.end();
         ++i)
    {
      Debug("parser") << "++ " << *i << std::endl;
    }
  }
  assert(!args.empty());
  // If operator already defined, just build application
  if (!p.d_expr.isNull())
  {
    // this happens with some arithmetic kinds, which are wrapped around
    // lambdas.
    args.insert(args.begin(), p.d_expr);
    return d_solver->mkTerm(api::APPLY_UF, args);
  }
  bool isBuiltinKind = false;
  // the builtin kind of the overall return expression
  api::Kind kind = api::NULL_EXPR;
  // First phase: piece operator together
  if (p.d_kind == api::NULL_EXPR)
  {
    // A non-built-in function application, get the expression
    api::Term v;
    if (isDeclared(p.d_name))
    {  // already appeared
      v = getVariable(p.d_name);
    }
    else
    {
      std::vector<api::Sort> sorts(args.size(), d_unsorted);
      api::Sort t =
          p.d_type == d_solver->getBooleanSort() ? p.d_type : d_unsorted;
      t = d_solver->mkFunctionSort(sorts, t);
      v = bindVar(p.d_name, t, ExprManager::VAR_FLAG_GLOBAL);  // levelZero
      preemptCommand(
          new DeclareFunctionCommand(p.d_name, v.getExpr(), t.getType()));
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
    assert(!v.isNull());
    checkFunctionLike(v);
    kind = getKindForFunction(v);
    args.insert(args.begin(), v);
  }
  else
  {
    kind = p.d_kind;
    isBuiltinKind = true;
  }
  assert(kind != api::NULL_EXPR);
  const Options& opts = d_solver->getOptions();
  // Second phase: apply parse op to the arguments
  if (isBuiltinKind)
  {
    if (!opts.getUfHo() && (kind == api::EQUAL || kind == api::DISTINCT))
    {
      // need --uf-ho if these operators are applied over function args
      for (std::vector<api::Term>::iterator i = args.begin(); i != args.end();
           ++i)
      {
        if ((*i).getSort().isFunction())
        {
          parseError(
              "Cannot apply equalty to functions unless --uf-ho is set.");
        }
      }
    }
    if (!strictModeEnabled() && (kind == api::AND || kind == api::OR)
        && args.size() == 1)
    {
      // Unary AND/OR can be replaced with the argument.
      return args[0];
    }
    if (kind == api::MINUS && args.size() == 1)
    {
      return d_solver->mkTerm(api::UMINUS, args[0]);
    }
    return d_solver->mkTerm(kind, args);
  }

  // check if partially applied function, in this case we use HO_APPLY
  if (args.size() >= 2)
  {
    api::Sort argt = args[0].getSort();
    if (argt.isFunction())
    {
      unsigned arity = argt.getFunctionArity();
      if (args.size() - 1 < arity)
      {
        if (!opts.getUfHo())
        {
          parseError("Cannot partially apply functions unless --uf-ho is set.");
        }
        Debug("parser") << "Partial application of " << args[0];
        Debug("parser") << " : #argTypes = " << arity;
        Debug("parser") << ", #args = " << args.size() - 1 << std::endl;
        // must curry the partial application
        return d_solver->mkTerm(api::HO_APPLY, args);
      }
    }
  }
  return d_solver->mkTerm(kind, args);
}

void Tptp::forceLogic(const std::string& logic)
{
  Parser::forceLogic(logic);
  preemptCommand(new SetBenchmarkLogicCommand(logic));
}

void Tptp::addFreeVar(api::Term var)
{
  assert(cnf());
  d_freeVar.push_back(var);
}

std::vector<api::Term> Tptp::getFreeVar()
{
  assert(cnf());
  std::vector<api::Term> r;
  r.swap(d_freeVar);
  return r;
}

api::Term Tptp::convertRatToUnsorted(api::Term expr)
{
  // Create the conversion function If they doesn't exists
  if (d_rtu_op.isNull()) {
    api::Sort t;
    // Conversion from rational to unsorted
    t = d_solver->mkFunctionSort(d_solver->getRealSort(), d_unsorted);
    d_rtu_op = d_solver->mkConst(t, "$$rtu");
    preemptCommand(
        new DeclareFunctionCommand("$$rtu", d_rtu_op.getExpr(), t.getType()));
    // Conversion from unsorted to rational
    t = d_solver->mkFunctionSort(d_unsorted, d_solver->getRealSort());
    d_utr_op = d_solver->mkConst(t, "$$utr");
    preemptCommand(
        new DeclareFunctionCommand("$$utr", d_utr_op.getExpr(), t.getType()));
  }
  // Add the inverse in order to show that over the elements that
  // appear in the problem there is a bijection between unsorted and
  // rational
  api::Term ret = d_solver->mkTerm(api::APPLY_UF, d_rtu_op, expr);
  if (d_r_converted.find(expr) == d_r_converted.end()) {
    d_r_converted.insert(expr);
    api::Term eq = d_solver->mkTerm(
        api::EQUAL, expr, d_solver->mkTerm(api::APPLY_UF, d_utr_op, ret));
    preemptCommand(new AssertCommand(eq.getExpr()));
  }
  return api::Term(ret);
}

api::Term Tptp::convertStrToUnsorted(std::string str)
{
  api::Term& e = d_distinct_objects[str];
  if (e.isNull())
  {
    e = d_solver->mkConst(d_unsorted, str);
  }
  return e;
}

api::Term Tptp::mkLambdaWrapper(api::Kind k, api::Sort argType)
{
  Debug("parser") << "mkLambdaWrapper: kind " << k << " and type " << argType
                  << "\n";
  std::vector<api::Term> lvars;
  std::vector<api::Sort> domainTypes = argType.getFunctionDomainSorts();
  for (unsigned i = 0, size = domainTypes.size(); i < size; ++i)
  {
    // the introduced variable is internal (not parsable)
    std::stringstream ss;
    ss << "_lvar_" << i;
    api::Term v = d_solver->mkVar(domainTypes[i], ss.str());
    lvars.push_back(v);
  }
  // apply body of lambda to variables
  api::Term wrapper =
      d_solver->mkTerm(api::LAMBDA,
                       d_solver->mkTerm(api::BOUND_VAR_LIST, lvars),
                       d_solver->mkTerm(k, lvars));

  return wrapper;
}

api::Term Tptp::getAssertionExpr(FormulaRole fr, api::Term expr)
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
      return d_solver->mkTerm(api::NOT, expr);
    case FR_UNKNOWN:
    case FR_FI_DOMAIN:
    case FR_FI_FUNCTORS:
    case FR_FI_PREDICATES:
    case FR_TYPE:
      // it does not correspond to an assertion
      return d_nullExpr;
      break;
  }
  assert(false);  // unreachable
  return d_nullExpr;
}

api::Term Tptp::getAssertionDistinctConstants()
{
  std::vector<api::Term> constants;
  for (std::pair<const std::string, api::Term>& cs : d_distinct_objects)
  {
    constants.push_back(cs.second);
  }
  if (constants.size() > 1)
  {
    return d_solver->mkTerm(api::DISTINCT, constants);
  }
  return d_nullExpr;
}

Command* Tptp::makeAssertCommand(FormulaRole fr,
                                 api::Term expr,
                                 bool cnf,
                                 bool inUnsatCore)
{
  // For SZS ontology compliance.
  // if we're in cnf() though, conjectures don't result in "Theorem" or
  // "CounterSatisfiable".
  if (!cnf && (fr == FR_NEGATED_CONJECTURE || fr == FR_CONJECTURE)) {
    d_hasConjecture = true;
    assert(!expr.isNull());
  }
  if( expr.isNull() ){
    return new EmptyCommand("Untreated role for expression");
  }else{
    return new AssertCommand(expr.getExpr(), inUnsatCore);
  }
}

}/* CVC4::parser namespace */
}/* CVC4 namespace */
