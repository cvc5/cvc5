/*********************                                                        */
/*! \file cvc3_compat.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Morgan Deters, Tim King, Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2016 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief CVC3 compatibility layer for CVC4
 **
 ** CVC3 compatibility layer for CVC4.
 **/

#include "compat/cvc3_compat.h"

#include <algorithm>
#include <cassert>
#include <iosfwd>
#include <iterator>
#include <sstream>
#include <string>

#include "base/exception.h"
#include "base/output.h"
#include "expr/expr_iomanip.h"
#include "expr/kind.h"
#include "expr/predicate.h"
#include "options/options.h"
#include "options/set_language.h"
#include "parser/parser.h"
#include "parser/parser_builder.h"
#include "smt/command.h"
#include "util/bitvector.h"
#include "util/hash.h"
#include "util/integer.h"
#include "util/rational.h"
#include "util/sexpr.h"
#include "util/subrange_bound.h"

using namespace std;

// Matches base/cvc4_assert.h's PrettyCheckArgument.
// base/cvc4_assert.h cannot be directly included.
#define CompatCheckArgument(cond, arg, msg...)         \
  do { \
    if(__builtin_expect( ( ! (cond) ), false )) { \
      throw ::CVC4::IllegalArgumentException(#cond, #arg, __PRETTY_FUNCTION__, \
                                             ::CVC4::IllegalArgumentException::formatVariadic(msg).c_str()); \
    } \
  } while(0)

#define Unimplemented(str) throw Exception(str)

namespace CVC3 {

// Connects ExprManagers to ValidityCheckers.  Needed to clean up the
// emmcs on ValidityChecker destruction (which are used for
// ExprManager-to-ExprManager import).
static std::map<CVC4::ExprManager*, ValidityChecker*> s_validityCheckers;

static std::hash_map<Type, Expr, CVC4::TypeHashFunction> s_typeToExpr;
static std::hash_map<Expr, Type, CVC4::ExprHashFunction> s_exprToType;

static bool typeHasExpr(const Type& t) {
  std::hash_map<Type, Expr, CVC4::TypeHashFunction>::const_iterator i = s_typeToExpr.find(t);
  return i != s_typeToExpr.end();
}

static Expr typeToExpr(const Type& t) {
  std::hash_map<Type, Expr, CVC4::TypeHashFunction>::const_iterator i = s_typeToExpr.find(t);
  assert(i != s_typeToExpr.end());
  return (*i).second;
}

static Type exprToType(const Expr& e) {
  std::hash_map<Expr, Type, CVC4::ExprHashFunction>::const_iterator i = s_exprToType.find(e);
  assert(i != s_exprToType.end());
  return (*i).second;
}

std::string int2string(int n) {
  std::ostringstream ss;
  ss << n;
  return ss.str();
}

std::ostream& operator<<(std::ostream& out, CLFlagType clft) {
  switch (clft) {
    case CLFLAG_NULL:
      out << "CLFLAG_NULL";
      break;
    case CLFLAG_BOOL:
      out << "CLFLAG_BOOL";
      break;
    case CLFLAG_INT:
      out << "CLFLAG_INT";
      break;
    case CLFLAG_STRING:
      out << "CLFLAG_STRING";
      break;
    case CLFLAG_STRVEC:
      out << "CLFLAG_STRVEC";
      break;
    default:
      out << "CLFlagType!UNKNOWN";
      break;
  }

  return out;
}

std::ostream& operator<<(std::ostream& out, QueryResult qr) {
  switch(qr) {
  case SATISFIABLE: out << "SATISFIABLE/INVALID"; break;
  case UNSATISFIABLE: out << "VALID/UNSATISFIABLE"; break;
  case ABORT: out << "ABORT"; break;
  case UNKNOWN: out << "UNKNOWN"; break;
  default: out << "QueryResult!UNKNOWN";
  }

  return out;
}

std::string QueryResultToString(QueryResult qr) {
  stringstream sstr;
  sstr << qr;
  return sstr.str();
}

std::ostream& operator<<(std::ostream& out, FormulaValue fv) {
  switch(fv) {
  case TRUE_VAL: out << "TRUE_VAL"; break;
  case FALSE_VAL: out << "FALSE_VAL"; break;
  case UNKNOWN_VAL: out << "UNKNOWN_VAL"; break;
  default: out << "FormulaValue!UNKNOWN";
  }

  return out;
}

std::ostream& operator<<(std::ostream& out, CVC3CardinalityKind c) {
  switch(c) {
  case CARD_FINITE: out << "CARD_FINITE"; break;
  case CARD_INFINITE: out << "CARD_INFINITE"; break;
  case CARD_UNKNOWN: out << "CARD_UNKNOWN"; break;
  default: out << "CVC3CardinalityKind!UNKNOWN";
  }

  return out;
}

static string toString(CLFlagType clft) {
  stringstream sstr;
  sstr << clft;
  return sstr.str();
}

bool operator==(const Cardinality& c, CVC3CardinalityKind d) {
  switch(d) {
  case CARD_FINITE:
    return c.isFinite();
  case CARD_INFINITE:
    return c.isInfinite();
  case CARD_UNKNOWN:
    return c.isUnknown();
  }

  throw Exception("internal error: CVC3 cardinality kind unhandled");
}

bool operator==(CVC3CardinalityKind d, const Cardinality& c) {
  return c == d;
}

bool operator!=(const Cardinality& c, CVC3CardinalityKind d) {
  return !(c == d);
}

bool operator!=(CVC3CardinalityKind d, const Cardinality& c) {
  return !(c == d);
}

Type::Type() :
  CVC4::Type() {
}

Type::Type(const CVC4::Type& type) :
  CVC4::Type(type) {
}

Type::Type(const Type& type) :
  CVC4::Type(type) {
}

Expr Type::getExpr() const {
  if(typeHasExpr(*this)) {
    return typeToExpr(*this);
  }
  Expr e = getExprManager()->mkVar("compatibility-layer-expr-type", *this);
  s_typeToExpr[*this] = e;
  s_exprToType[e] = *this;
  s_validityCheckers[e.getExprManager()]->d_exprTypeMapRemove.push_back(e);
  return e;
}

int Type::arity() const {
  return isSort() ? CVC4::SortType(*this).getParamTypes().size() : 0;
}

Type Type::operator[](int i) const {
  return Type(CVC4::Type(CVC4::SortType(*this).getParamTypes()[i]));
}

bool Type::isBool() const {
  return isBoolean();
}

bool Type::isSubtype() const {
  return false;
}

Cardinality Type::card() const {
  return getCardinality();
}

Expr Type::enumerateFinite(Unsigned n) const {
  Unimplemented("This CVC3 compatibility function not yet implemented (sorry!)");
}

Unsigned Type::sizeFinite() const {
  return getCardinality().getFiniteCardinality().getUnsignedLong();
}

Type Type::typeBool(ExprManager* em) {
  return Type(CVC4::Type(em->booleanType()));
}

Type Type::funType(const std::vector<Type>& typeDom,
                   const Type& typeRan) {
  const vector<CVC4::Type>& dom =
    *reinterpret_cast<const vector<CVC4::Type>*>(&typeDom);
  return Type(typeRan.getExprManager()->mkFunctionType(dom, typeRan));
}

Type Type::funType(const Type& typeRan) const {
  return Type(getExprManager()->mkFunctionType(*this, typeRan));
}

Expr::Expr() : CVC4::Expr() {
}

Expr::Expr(const Expr& e) : CVC4::Expr(e) {
}

Expr::Expr(const CVC4::Expr& e) : CVC4::Expr(e) {
}

Expr::Expr(const CVC4::Kind k) : CVC4::Expr() {
  *this = getEM()->operatorOf(k);
}

Expr Expr::eqExpr(const Expr& right) const {
  return getEM()->mkExpr(CVC4::kind::EQUAL, *this, right);
}

Expr Expr::notExpr() const {
  return getEM()->mkExpr(CVC4::kind::NOT, *this);
}

Expr Expr::negate() const {
  // avoid double-negatives
  return (getKind() == CVC4::kind::NOT) ?
    (*this)[0] :
    Expr(getEM()->mkExpr(CVC4::kind::NOT, *this));
}

Expr Expr::andExpr(const Expr& right) const {
  return getEM()->mkExpr(CVC4::kind::AND, *this, right);
}

Expr Expr::orExpr(const Expr& right) const {
  return getEM()->mkExpr(CVC4::kind::OR, *this, right);
}

Expr Expr::iteExpr(const Expr& thenpart, const Expr& elsepart) const {
  return getEM()->mkExpr(CVC4::kind::ITE, *this, thenpart, elsepart);
}

Expr Expr::iffExpr(const Expr& right) const {
  return getEM()->mkExpr(CVC4::kind::IFF, *this, right);
}

Expr Expr::impExpr(const Expr& right) const {
  return getEM()->mkExpr(CVC4::kind::IMPLIES, *this, right);
}

Expr Expr::xorExpr(const Expr& right) const {
  return getEM()->mkExpr(CVC4::kind::XOR, *this, right);
}

Expr Expr::substExpr(const std::vector<Expr>& oldTerms,
                     const std::vector<Expr>& newTerms) const {
  const vector<CVC4::Expr>& o =
    *reinterpret_cast<const vector<CVC4::Expr>*>(&oldTerms);
  const vector<CVC4::Expr>& n =
    *reinterpret_cast<const vector<CVC4::Expr>*>(&newTerms);

  return Expr(substitute(o, n));
}

Expr Expr::substExpr(const ExprHashMap<Expr>& oldToNew) const {
  const hash_map<CVC4::Expr, CVC4::Expr, CVC4::ExprHashFunction>& o2n =
    *reinterpret_cast<const hash_map<CVC4::Expr, CVC4::Expr, CVC4::ExprHashFunction>*>(&oldToNew);

  return Expr(substitute(o2n));
}

Expr Expr::operator!() const {
  return notExpr();
}

Expr Expr::operator&&(const Expr& right) const {
  return andExpr(right);
}

Expr Expr::operator||(const Expr& right) const {
  return orExpr(right);
}

size_t Expr::hash(const Expr& e) {
  return CVC4::ExprHashFunction()(e);
}

size_t Expr::hash() const {
  return CVC4::ExprHashFunction()(*this);
}

bool Expr::isFalse() const {
  return getKind() == CVC4::kind::CONST_BOOLEAN && getConst<bool>() == false;
}

bool Expr::isTrue() const {
  return getKind() == CVC4::kind::CONST_BOOLEAN && getConst<bool>() == true;
}

bool Expr::isBoolConst() const {
  return getKind() == CVC4::kind::CONST_BOOLEAN;
}

bool Expr::isVar() const {
  return isVariable();
}

bool Expr::isString() const {
  return getType().isString();
}

bool Expr::isBoundVar() const {
  return getKind() == CVC4::kind::BOUND_VARIABLE;
}

bool Expr::isForall() const {
  return getKind() == CVC4::kind::FORALL;
}

bool Expr::isExists() const {
  return getKind() == CVC4::kind::EXISTS;
}

bool Expr::isLambda() const {
  return getKind() == CVC4::kind::LAMBDA;
}

bool Expr::isClosure() const {
  return isQuantifier() || isLambda();
}

bool Expr::isQuantifier() const {
  return getKind() == CVC4::kind::FORALL || getKind() == CVC4::kind::EXISTS;
}

bool Expr::isApply() const {
  return hasOperator();
}

bool Expr::isSymbol() const {
  Unimplemented("This CVC3 compatibility function not yet implemented (sorry!)");
}

bool Expr::isTheorem() const {
  return false;
}

bool Expr::isType() const {
  return s_exprToType.find(*this) != s_exprToType.end();
}

bool Expr::isTerm() const {
  return !getType().isBool();
}

bool Expr::isConstant() const {
  return isConst();
}

bool Expr::isRawList() const {
  return false;
}

bool Expr::isAtomic() const {
  if (getType().isBool()) {
    return isBoolConst();
  }
  for (int k = 0; k < arity(); ++k) {
    if (!(*this)[k].isAtomic()) {
      return false;
    }
  }
  return true;
}

bool Expr::isAtomicFormula() const {
  if (!getType().isBool()) {
    return false;
  }
  switch(getKind()) {
    case CVC4::kind::FORALL:
    case CVC4::kind::EXISTS:
    case CVC4::kind::XOR:
    case CVC4::kind::NOT:
    case CVC4::kind::AND:
    case CVC4::kind::OR:
    case CVC4::kind::ITE:
    case CVC4::kind::IFF:
    case CVC4::kind::IMPLIES:
      return false;
    default:
      ; /* fall through */
  }
  for (Expr::iterator k = begin(), kend=end(); k != kend; ++k) {
    if (!CVC3::Expr(*k).isAtomic()) {
      return false;
    }
  }
  return true;
}

bool Expr::isAbsAtomicFormula() const {
  return isQuantifier() || isAtomicFormula();
}

bool Expr::isLiteral() const {
  return isAtomicFormula() || (isNot() && (*this)[0].isAtomicFormula());
}

bool Expr::isAbsLiteral() const {
  return isAbsAtomicFormula() || (isNot() && (*this)[0].isAbsAtomicFormula());
}

bool Expr::isBoolConnective() const {
  if (!getType().isBool()) {
    return false;
  }
  switch (getKind()) {
  case CVC4::kind::NOT:
  case CVC4::kind::AND:
  case CVC4::kind::OR:
  case CVC4::kind::IMPLIES:
  case CVC4::kind::IFF:
  case CVC4::kind::XOR:
  case CVC4::kind::ITE:
    return true;
  default:
    return false;
  }
}

bool Expr::isPropLiteral() const {
  return (isNot() && (*this)[0].isPropAtom()) || isPropAtom();
}

bool Expr::isPropAtom() const {
  return !isTerm() && !isBoolConnective();
}

std::string Expr::getName() const {
  Unimplemented("This CVC3 compatibility function not yet implemented (sorry!)");
}

std::string Expr::getUid() const {
  Unimplemented("This CVC3 compatibility function not yet implemented (sorry!)");
}

std::string Expr::getString() const {
  CompatCheckArgument(getKind() == CVC4::kind::CONST_STRING, *this, "CVC3::Expr::getString(): not a string Expr: `%s'", toString().c_str());
  return getConst<CVC4::String>().toString();
}

std::vector<Expr> Expr::getVars() const {
  CompatCheckArgument(isClosure(), *this, "CVC3::Expr::getVars(): not a closure Expr: `%s'", toString().c_str());
  const vector<CVC4::Expr>& kids = (*this)[0].getChildren();
  vector<Expr> v;
  for(vector<CVC4::Expr>::const_iterator i = kids.begin(); i != kids.end(); ++i) {
    v.push_back(*i);
  }
  return v;
}

Expr Expr::getExistential() const {
  Unimplemented("This CVC3 compatibility function not yet implemented (sorry!)");
}

int Expr::getBoundIndex() const {
  Unimplemented("This CVC3 compatibility function not yet implemented (sorry!)");
}

Expr Expr::getBody() const {
  CompatCheckArgument(isClosure(), *this, "CVC3::Expr::getBody(): not a closure Expr: `%s'", toString().c_str());
  return (*this)[1];
}

Theorem Expr::getTheorem() const {
  Unimplemented("This CVC3 compatibility function not yet implemented (sorry!)");
}

bool Expr::isEq() const {
  return getKind() == CVC4::kind::EQUAL;
}

bool Expr::isNot() const {
  return getKind() == CVC4::kind::NOT;
}

bool Expr::isAnd() const {
  return getKind() == CVC4::kind::AND;
}

bool Expr::isOr() const {
  return getKind() == CVC4::kind::OR;
}

bool Expr::isITE() const {
  return getKind() == CVC4::kind::ITE;
}

bool Expr::isIff() const {
  return getKind() == CVC4::kind::IFF;
}

bool Expr::isImpl() const {
  return getKind() == CVC4::kind::IMPLIES;
}

bool Expr::isXor() const {
  return getKind() == CVC4::kind::XOR;
}

bool Expr::isRational() const {
  return getKind() == CVC4::kind::CONST_RATIONAL;
}

bool Expr::isSkolem() const {
  return getKind() == CVC4::kind::SKOLEM;
}

const Rational& Expr::getRational() const {
  CompatCheckArgument(isRational(), *this, "CVC3::Expr::getRational(): not a rational Expr: `%s'", toString().c_str());
  return getConst<CVC4::Rational>();
}

Op Expr::mkOp() const {
  return *this;
}

Op Expr::getOp() const {
  return getOperator();
}

Expr Expr::getOpExpr() const {
  return getOperator();
}

int Expr::getOpKind() const {
  Expr op = getOperator();
  int k = op.getKind();
  return k == BUILTIN ? getKind() : k;
}

Expr Expr::getExpr() const {
  return *this;
}

std::vector< std::vector<Expr> > Expr::getTriggers() const {
  CompatCheckArgument(isClosure(), *this,
                      "getTriggers() called on non-closure expr");
  if(getNumChildren() < 3) {
    // no triggers for this quantifier
    return vector< vector<Expr> >();
  } else {
    // get the triggers from the third child
    Expr triggers = (*this)[2];
    vector< vector<Expr> > v;
    for(const_iterator i = triggers.begin(); i != triggers.end(); ++i) {
      v.push_back(vector<Expr>());
      for(const_iterator j = (*i).begin(); j != (*i).end(); ++j) {
        v.back().push_back(*j);
      }
    }
    return v;
  }
}

ExprManager* Expr::getEM() const {
  return reinterpret_cast<ExprManager*>(getExprManager());
}

std::vector<Expr> Expr::getKids() const {
  vector<CVC4::Expr> v = getChildren();
  return *reinterpret_cast<vector<Expr>*>(&v);
}

ExprIndex Expr::getIndex() const {
  return getId();
}

int Expr::arity() const {
  return getNumChildren();
}

Expr Expr::unnegate() const {
  return isNot() ? Expr((*this)[0]) : *this;
}

bool Expr::isInitialized() const {
  return !isNull();
}

Type Expr::getType() const {
  return Type(this->CVC4::Expr::getType());
}

Type Expr::lookupType() const {
  return getType();
}

void Expr::pprint() const {
  std::cout << *this << std::endl;
}

void Expr::pprintnodag() const {
  CVC4::expr::ExprDag::Scope scope(std::cout, 0);
  std::cout << *this << std::endl;
}

bool isArrayLiteral(const Expr& e) {
  Unimplemented("This CVC3 compatibility function not yet implemented (sorry!)");
}

std::string ExprManager::getKindName(int kind) {
  return CVC4::kind::kindToString(CVC4::Kind(kind));
}

InputLanguage ExprManager::getInputLang() const {
  return getOptions().getInputLanguage();
}

InputLanguage ExprManager::getOutputLang() const {
  return CVC4::language::toInputLanguage(getOptions().getOutputLanguage());
}

Expr Expr::operator[](int i) const {
  return Expr(this->CVC4::Expr::operator[](i));
}

CLFlag::CLFlag(bool b, const std::string& help, bool display) :
  d_tp(CLFLAG_BOOL) {
  d_data.b = b;
}

CLFlag::CLFlag(int i, const std::string& help, bool display) :
  d_tp(CLFLAG_INT) {
  d_data.i = i;
}

CLFlag::CLFlag(const std::string& s, const std::string& help, bool display) :
  d_tp(CLFLAG_STRING) {
  d_data.s = new string(s);
}

CLFlag::CLFlag(const char* s, const std::string& help, bool display) :
  d_tp(CLFLAG_STRING) {
  d_data.s = new string(s);
}

CLFlag::CLFlag(const std::vector<std::pair<string,bool> >& sv,
               const std::string& help, bool display) :
  d_tp(CLFLAG_STRVEC) {
  d_data.sv = new vector<pair<string, bool> >(sv);
}

CLFlag::CLFlag() :
  d_tp(CLFLAG_NULL) {
}

CLFlag::CLFlag(const CLFlag& f) :
  d_tp(f.d_tp) {
  switch(d_tp) {
  case CLFLAG_STRING:
    d_data.s = new string(*f.d_data.s);
    break;
  case CLFLAG_STRVEC:
    d_data.sv = new vector<pair<string, bool> >(*f.d_data.sv);
    break;
  default:
    d_data = f.d_data;
  }
}

CLFlag::~CLFlag() {
  switch(d_tp) {
  case CLFLAG_STRING:
    delete d_data.s;
    break;
  case CLFLAG_STRVEC:
    delete d_data.sv;
    break;
  default:
    ; // nothing to do
  }
}

CLFlag& CLFlag::operator=(const CLFlag& f) {
  if(this == &f) {
    // self-assignment
    return *this;
  }

  // try to preserve the existing heap objects if possible
  if(d_tp == f.d_tp) {
    switch(d_tp) {
    case CLFLAG_STRING:
      *d_data.s = *f.d_data.s;
      break;
    case CLFLAG_STRVEC:
      *d_data.sv = *f.d_data.sv;
      break;
    default:
      d_data = f.d_data;
    }
  } else {
    switch(d_tp) {
    case CLFLAG_STRING:
      delete d_data.s;
      break;
    case CLFLAG_STRVEC:
      delete d_data.sv;
      break;
    default:
      ; // nothing to do here
    }

    switch(f.d_tp) {
    case CLFLAG_STRING:
      d_data.s = new string(*f.d_data.s);
      break;
    case CLFLAG_STRVEC:
      d_data.sv = new vector<pair<string, bool> >(*f.d_data.sv);
      break;
    default:
      d_data = f.d_data;
    }
  }
  d_tp = f.d_tp;
  return *this;
}

CLFlag& CLFlag::operator=(bool b) {
  CompatCheckArgument(d_tp == CLFLAG_BOOL, this);
  d_data.b = b;
  return *this;
}

CLFlag& CLFlag::operator=(int i) {
  CompatCheckArgument(d_tp == CLFLAG_INT, this);
  d_data.i = i;
  return *this;
}

CLFlag& CLFlag::operator=(const std::string& s) {
  CompatCheckArgument(d_tp == CLFLAG_STRING, this);
  *d_data.s = s;
  return *this;
}

CLFlag& CLFlag::operator=(const char* s) {
  CompatCheckArgument(d_tp == CLFLAG_STRING, this);
  *d_data.s = s;
  return *this;
}

CLFlag& CLFlag::operator=(const std::pair<string, bool>& p) {
  CompatCheckArgument(d_tp == CLFLAG_STRVEC, this);
  d_data.sv->push_back(p);
  return *this;
}

CLFlag& CLFlag::operator=(const std::vector<std::pair<string, bool> >& sv) {
  CompatCheckArgument(d_tp == CLFLAG_STRVEC, this);
  *d_data.sv = sv;
  return *this;
}

CLFlagType CLFlag::getType() const {
  return d_tp;
}

bool CLFlag::modified() const {
  Unimplemented("This CVC3 compatibility function not yet implemented (sorry!)");
}

bool CLFlag::display() const {
  Unimplemented("This CVC3 compatibility function not yet implemented (sorry!)");
}

const bool& CLFlag::getBool() const {
  CompatCheckArgument(d_tp == CLFLAG_BOOL, this);
  return d_data.b;
}

const int& CLFlag::getInt() const {
  CompatCheckArgument(d_tp == CLFLAG_INT, this);
  return d_data.i;
}

const std::string& CLFlag::getString() const {
  CompatCheckArgument(d_tp == CLFLAG_STRING, this);
  return *d_data.s;
}

const std::vector<std::pair<string, bool> >& CLFlag::getStrVec() const {
  CompatCheckArgument(d_tp == CLFLAG_STRVEC, this);
  return *d_data.sv;
}

const std::string& CLFlag::getHelp() const {
  Unimplemented("This CVC3 compatibility function not yet implemented (sorry!)");
}

void CLFlags::addFlag(const std::string& name, const CLFlag& f) {
  d_map[name] = f;
}

size_t CLFlags::countFlags(const std::string& name) const {
  Unimplemented("This CVC3 compatibility function not yet implemented (sorry!)");
}

size_t CLFlags::countFlags(const std::string& name,
                           std::vector<std::string>& names) const {
  Unimplemented("This CVC3 compatibility function not yet implemented (sorry!)");
}

const CLFlag& CLFlags::getFlag(const std::string& name) const {
  FlagMap::const_iterator i = d_map.find(name);
  CompatCheckArgument(i != d_map.end(), name, "No command-line flag by that name, or not supported.");
  return (*i).second;
}

const CLFlag& CLFlags::operator[](const std::string& name) const {
  return getFlag(name);
}

void CLFlags::setFlag(const std::string& name, const CLFlag& f) {
  FlagMap::iterator i = d_map.find(name);
  CompatCheckArgument(i != d_map.end(), name, "No command-line flag by that name, or not supported.");
  CompatCheckArgument((*i).second.getType() == f.getType(), f,
                      "Command-line flag `%s' has type %s, but caller tried to set to a %s.",
                      name.c_str(),
                      toString((*i).second.getType()).c_str(),
                      toString(f.getType()).c_str());
  (*i).second = f;
}

void CLFlags::setFlag(const std::string& name, bool b) {
  FlagMap::iterator i = d_map.find(name);
  CompatCheckArgument(i != d_map.end(), name, "No command-line flag by that name, or not supported.");
  (*i).second = b;
}

void CLFlags::setFlag(const std::string& name, int i) {
  FlagMap::iterator it = d_map.find(name);
  CompatCheckArgument(it != d_map.end(), name, "No command-line flag by that name, or not supported.");
  (*it).second = i;
}

void CLFlags::setFlag(const std::string& name, const std::string& s) {
  FlagMap::iterator i = d_map.find(name);
  CompatCheckArgument(i != d_map.end(), name, "No command-line flag by that name, or not supported.");
  (*i).second = s;
}

void CLFlags::setFlag(const std::string& name, const char* s) {
  FlagMap::iterator i = d_map.find(name);
  CompatCheckArgument(i != d_map.end(), name, "No command-line flag by that name, or not supported.");
  (*i).second = s;
}

void CLFlags::setFlag(const std::string& name, const std::pair<string, bool>& p) {
  FlagMap::iterator i = d_map.find(name);
  CompatCheckArgument(i != d_map.end(), name, "No command-line flag by that name, or not supported.");
  (*i).second = p;
}

void CLFlags::setFlag(const std::string& name,
                      const std::vector<std::pair<string, bool> >& sv) {
  FlagMap::iterator i = d_map.find(name);
  CompatCheckArgument(i != d_map.end(), name, "No command-line flag by that name, or not supported.");
  (*i).second = sv;
}

void ValidityChecker::setUpOptions(CVC4::Options& options, const CLFlags& clflags) {
  // always incremental and model-producing in CVC3 compatibility mode
  // also incrementally-simplifying and interactive
  d_smt->setOption("incremental", string("true"));
  // disable this option by default for now, because datatype models
  // are broken [MGD 10/4/2012]
  //d_smt->setOption("produce-models", string("true"));
  d_smt->setOption("simplification-mode", string("incremental"));
  d_smt->setOption("interactive-mode", string("true"));// support SmtEngine::getAssertions()

  d_smt->setOption("statistics", string(clflags["stats"].getBool() ? "true" : "false"));
  d_smt->setOption("random-seed", int2string(clflags["seed"].getInt()));
  d_smt->setOption("parse-only", string(clflags["parse-only"].getBool() ? "true" : "false"));
  d_smt->setOption("input-language", clflags["lang"].getString());
  if(clflags["output-lang"].getString() == "") {
    stringstream langss;
    langss << CVC4::language::toOutputLanguage(options.getInputLanguage());
    d_smt->setOption("output-language", langss.str());
  } else {
    d_smt->setOption("output-language", clflags["output-lang"].getString());
  }
}

ValidityChecker::ValidityChecker() :
  d_clflags(new CLFlags()),
  d_options(),
  d_em(NULL),
  d_emmc(),
  d_reverseEmmc(),
  d_smt(NULL),
  d_parserContext(NULL),
  d_exprTypeMapRemove(),
  d_stackLevel(0),
  d_constructors(),
  d_selectors() {
  d_em = reinterpret_cast<ExprManager*>(new CVC4::ExprManager(d_options));
  s_validityCheckers[d_em] = this;
  d_smt = new CVC4::SmtEngine(d_em);
  setUpOptions(d_options, *d_clflags);
  d_parserContext = CVC4::parser::ParserBuilder(d_em, "<internal>").withInputLanguage(CVC4::language::input::LANG_CVC4).withStringInput("").build();
}

ValidityChecker::ValidityChecker(const CLFlags& clflags) :
  d_clflags(new CLFlags(clflags)),
  d_options(),
  d_em(NULL),
  d_emmc(),
  d_reverseEmmc(),
  d_smt(NULL),
  d_parserContext(NULL),
  d_exprTypeMapRemove(),
  d_stackLevel(0),
  d_constructors(),
  d_selectors() {
  d_em = reinterpret_cast<ExprManager*>(new CVC4::ExprManager(d_options));
  s_validityCheckers[d_em] = this;
  d_smt = new CVC4::SmtEngine(d_em);
  setUpOptions(d_options, *d_clflags);
  d_parserContext = CVC4::parser::ParserBuilder(d_em, "<internal>").withInputLanguage(CVC4::language::input::LANG_CVC4).withStringInput("").build();
}

ValidityChecker::~ValidityChecker() {
  for(vector<Expr>::iterator i = d_exprTypeMapRemove.begin(); i != d_exprTypeMapRemove.end(); ++i) {
    s_typeToExpr.erase(s_exprToType[*i]);
    s_exprToType.erase(*i);
  }
  d_exprTypeMapRemove.clear();
  delete d_parserContext;
  delete d_smt;
  d_emmc.clear();
  for(set<ValidityChecker*>::iterator i = d_reverseEmmc.begin(); i != d_reverseEmmc.end(); ++i) {
    (*i)->d_emmc.erase(d_em);
  }
  d_reverseEmmc.clear();
  s_validityCheckers.erase(d_em);
  delete d_em;
  delete d_clflags;
}

CLFlags& ValidityChecker::getFlags() const {
  return *d_clflags;
}

void ValidityChecker::reprocessFlags() {
  Unimplemented("This CVC3 compatibility function not yet implemented (sorry!)");
}

CLFlags ValidityChecker::createFlags() {
  CLFlags flags;

  // We expect the user to type cvc3 -h to get help, which will set
  // the "help" flag to false; that's why it's initially true.

  // Overall system control flags
  flags.addFlag("timeout", CLFlag(0, "Kill cvc3 process after given number of seconds (0==no limit)"));
  flags.addFlag("stimeout", CLFlag(0, "Set time resource limit in tenths of seconds for a query(0==no limit)"));
  flags.addFlag("resource", CLFlag(0, "Set finite resource limit (0==no limit)"));
  flags.addFlag("mm", CLFlag("chunks", "Memory manager (chunks, malloc)"));

  // Information printing flags
  flags.addFlag("help",CLFlag(true, "print usage information and exit"));
  flags.addFlag("unsupported",CLFlag(true, "print usage for old/unsupported/experimental options"));
  flags.addFlag("version",CLFlag(true, "print version information and exit"));
  flags.addFlag("interactive", CLFlag(false, "Interactive mode"));
  flags.addFlag("stats", CLFlag(false, "Print run-time statistics"));
  flags.addFlag("seed", CLFlag(91648253, "Set the seed for random sequence"));
  flags.addFlag("printResults", CLFlag(true, "Print results of interactive commands."));
  flags.addFlag("dump-log", CLFlag("", "Dump API call log in CVC3 input "
                                   "format to given file "
                                   "(off when file name is \"\")"));
  flags.addFlag("parse-only", CLFlag(false,"Parse the input, then exit."));

  //Translation related flags
  flags.addFlag("expResult", CLFlag("", "For smtlib translation.  Give the expected result", false));
  flags.addFlag("category", CLFlag("unknown", "For smtlib translation.  Give the category", false));
  flags.addFlag("translate", CLFlag(false, "Produce a complete translation from "
                                    "the input language to output language.  "));
  flags.addFlag("real2int", CLFlag(false, "When translating, convert reals to integers.", false));
  flags.addFlag("convertArith", CLFlag(false, "When translating, try to rewrite arith terms into smt-lib subset", false));
  flags.addFlag("convert2diff", CLFlag("", "When translating, try to force into difference logic.  Legal values are int and real.", false));
  flags.addFlag("iteLiftArith", CLFlag(false, "For translation.  If true, ite's are lifted out of arith exprs.", false));
  flags.addFlag("convertArray", CLFlag(false, "For translation.  If true, arrays are converted to uninterpreted functions if possible.", false));
  flags.addFlag("combineAssump", CLFlag(false, "For translation.  If true, assumptions are combined into the query.", false));
  flags.addFlag("convert2array", CLFlag(false, "For translation. If true, try to convert to array-only theory", false));
  flags.addFlag("convertToBV",CLFlag(0, "For translation.  Set to nonzero to convert ints to bv's of that length", false));
  flags.addFlag("convert-eq-iff",CLFlag(false, "Convert equality on Boolean expressions to iff.", false));
  flags.addFlag("preSimplify",CLFlag(false, "Simplify each assertion or query before translating it", false));
  flags.addFlag("dump-tcc", CLFlag(false, "Compute and dump TCC only"));
  flags.addFlag("trans-skip-pp", CLFlag(false, "Skip preprocess step in translation module", false));
  flags.addFlag("trans-skip-difficulty", CLFlag(false, "Leave out difficulty attribute during translation to SMT v2.0", false));
  flags.addFlag("promote", CLFlag(true, "Promote undefined logic combinations to defined logic combinations during translation to SMT", false));

  // Parser related flags
  flags.addFlag("old-func-syntax",CLFlag(false, "Enable parsing of old-style function syntax", false));

  // Pretty-printing related flags
  flags.addFlag("dagify-exprs",
                CLFlag(true, "Print expressions with sharing as DAGs"));
  flags.addFlag("lang", CLFlag("presentation", "Input language "
                               "(presentation, smt, smt2, internal)"));
  flags.addFlag("output-lang", CLFlag("", "Output language "
                                      "(presentation, smtlib, simplify, internal, lisp, tptp, spass)"));
  flags.addFlag("indent", CLFlag(false, "Print expressions with indentation"));
  flags.addFlag("width", CLFlag(80, "Suggested line width for printing"));
  flags.addFlag("print-depth", CLFlag(-1, "Max. depth to print expressions "));
  flags.addFlag("print-assump", CLFlag(false, "Print assumptions in Theorems "));

  // Search Engine (SAT) related flags
  flags.addFlag("sat",CLFlag("minisat", "choose a SAT solver to use "
                             "(sat, minisat)"));
  flags.addFlag("de",CLFlag("dfs", "choose a decision engine to use "
                            "(dfs, sat)"));

  // Proofs and Assumptions
  flags.addFlag("proofs", CLFlag(false, "Produce proofs"));
  flags.addFlag("check-proofs", CLFlag(false, "Check proofs on-the-fly"));
  flags.addFlag("minimizeClauses", CLFlag(false, "Use brute-force minimization of clauses", false));
  flags.addFlag("dynack", CLFlag(false, "Use dynamic Ackermannization", false));
  flags.addFlag("smart-clauses", CLFlag(true, "Learn multiple clauses per conflict"));
  // Core framework switches
  flags.addFlag("tcc", CLFlag(false, "Check TCCs for each ASSERT and QUERY"));
  flags.addFlag("cnf", CLFlag(true, "Convert top-level Boolean formulas to CNF", false));
  flags.addFlag("ignore-cnf-vars", CLFlag(false, "Do not split on aux. CNF vars (with +cnf)", false));
  flags.addFlag("orig-formula", CLFlag(false, "Preserve the original formula with +cnf (for splitter heuristics)", false));
  flags.addFlag("liftITE", CLFlag(false, "Eagerly lift all ITE exprs"));
  flags.addFlag("iflift", CLFlag(false, "Translate if-then-else terms to CNF (with +cnf)", false));
  flags.addFlag("circuit", CLFlag(false, "With +cnf, use circuit propagation", false));
  flags.addFlag("un-ite-ify", CLFlag(false, "Unconvert ITE expressions", false));
  flags.addFlag("ite-cond-simp",
                CLFlag(false, "Replace ITE condition by TRUE/FALSE in subexprs", false));
  flags.addFlag("preprocess", CLFlag(true, "Preprocess queries"));
  flags.addFlag("pp-pushneg", CLFlag(false, "Push negation in preprocessor"));
  flags.addFlag("pp-bryant", CLFlag(false, "Enable Bryant algorithm for UF", false));
  flags.addFlag("pp-budget", CLFlag(0, "Budget for new preprocessing step", false));
  flags.addFlag("pp-care", CLFlag(true, "Enable care-set preprocessing step", false));
  flags.addFlag("simp-and", CLFlag(false, "Rewrite x&y to x&y[x/true]", false));
  flags.addFlag("simp-or", CLFlag(false, "Rewrite x|y to x|y[x/false]", false));
  flags.addFlag("pp-batch", CLFlag(false, "Ignore assumptions until query, then process all at once"));

  // Negate the query when translate into tptp
  flags.addFlag("negate-query", CLFlag(true, "Negate the query when translate into TPTP format"));;

  // Concrete model generation (counterexamples) flags
  flags.addFlag("counterexample", CLFlag(false, "Dump counterexample if formula is invalid or satisfiable"));
  flags.addFlag("model", CLFlag(false, "Dump model if formula is invalid or satisfiable"));
  flags.addFlag("unknown-check-model", CLFlag(false, "Try to generate model if formula is unknown"));
  flags.addFlag("applications", CLFlag(true, "Add relevant function applications and array accesses to the concrete countermodel"));
  // Debugging flags (only for the debug build)
  // #ifdef _CVC3_DEBUG_MODE
  vector<pair<string,bool> > sv;
  flags.addFlag("trace", CLFlag(sv, "Tracing.  Multiple flags add up."));
  flags.addFlag("dump-trace", CLFlag("", "Dump debugging trace to "
                                   "given file (off when file name is \"\")"));
  // #endif
  // DP-specific flags

  // Arithmetic
  flags.addFlag("arith-new",CLFlag(false, "Use new arithmetic dp", false));
  flags.addFlag("arith3",CLFlag(false, "Use old arithmetic dp that works well with combined theories", false));
  flags.addFlag("var-order",
                CLFlag(false, "Use simple variable order in arith", false));
  flags.addFlag("ineq-delay", CLFlag(0, "Accumulate this many inequalities before processing (-1 for don't process until necessary)"));

  flags.addFlag("nonlinear-sign-split", CLFlag(true, "Whether to split on the signs of nontrivial nonlinear terms"));

  flags.addFlag("grayshadow-threshold", CLFlag(-1, "Ignore gray shadows bigger than this (makes solver incomplete)"));
  flags.addFlag("pathlength-threshold", CLFlag(-1, "Ignore gray shadows bigger than this (makes solver incomplete)"));

  // Arrays
  flags.addFlag("liftReadIte", CLFlag(true, "Lift read of ite"));

  //for LFSC stuff, disable Tseitin CNF conversion, by Yeting
  flags.addFlag("cnf-formula", CLFlag(false, "The input must be in CNF. This option automatically enables '-de sat' and disable preprocess"));

  //for LFSC print out, by Yeting
  //flags.addFlag("lfsc", CLFlag(false, "the input is already in CNF. This option automatically enables -de sat and disable -preprocess"));

  // for LFSC print, allows different modes by Liana
  flags.addFlag("lfsc-mode",
                  CLFlag(0, "lfsc mode 0: off, 1:normal, 2:cvc3-mimic etc."));


  // Quantifiers
  flags.addFlag("max-quant-inst", CLFlag(200, "The maximum number of"
                                " naive instantiations"));

  flags.addFlag("quant-new",
                 CLFlag(true, "If this option is false, only naive instantiation is called"));

  flags.addFlag("quant-lazy", CLFlag(false, "Instantiate lazily", false));

  flags.addFlag("quant-sem-match",
                CLFlag(false, "Attempt to match semantically when instantiating", false));

//   flags.addFlag("quant-const-match",
//                 CLFlag(true, "When matching semantically, only match with constants", false));

  flags.addFlag("quant-complete-inst",
                CLFlag(false, "Try complete instantiation heuristic.  +pp-batch will be automatically enabled"));

  flags.addFlag("quant-max-IL",
                CLFlag(100, "The maximum Instantiation Level allowed"));

  flags.addFlag("quant-inst-lcache",
                CLFlag(true, "Cache instantiations"));

  flags.addFlag("quant-inst-gcache",
                CLFlag(false, "Cache instantiations", false));

  flags.addFlag("quant-inst-tcache",
                CLFlag(false, "Cache instantiations", false));


  flags.addFlag("quant-inst-true",
                CLFlag(true, "Ignore true instantiations"));

  flags.addFlag("quant-pullvar",
                CLFlag(false, "Pull out vars", false));

  flags.addFlag("quant-score",
                CLFlag(true, "Use instantiation level"));

  flags.addFlag("quant-polarity",
                CLFlag(false, "Use polarity ", false));

  flags.addFlag("quant-eqnew",
                CLFlag(true, "Use new equality matching"));

  flags.addFlag("quant-max-score",
                CLFlag(0, "Maximum initial dynamic score"));

  flags.addFlag("quant-trans3",
                CLFlag(true, "Use trans heuristic"));

  flags.addFlag("quant-trans2",
                CLFlag(true, "Use trans2 heuristic"));

  flags.addFlag("quant-naive-num",
                CLFlag(1000, "Maximum number to call naive instantiation"));

  flags.addFlag("quant-naive-inst",
                CLFlag(true, "Use naive instantiation"));

  flags.addFlag("quant-man-trig",
                CLFlag(true, "Use manual triggers"));

  flags.addFlag("quant-gfact",
                CLFlag(false, "Send facts to core directly", false));

  flags.addFlag("quant-glimit",
                CLFlag(1000, "Limit for gfacts", false));

  flags.addFlag("print-var-type", //by yeting, as requested by Sascha Boehme for proofs
                CLFlag(false, "Print types for bound variables"));

  // Bitvectors
  flags.addFlag("bv32-flag",
                CLFlag(false, "assume that all bitvectors are 32bits with no overflow", false));

  // Uninterpreted Functions
  flags.addFlag("trans-closure",
                CLFlag(false,"enables transitive closure of binary relations", false));

  // Datatypes
  flags.addFlag("dt-smartsplits",
                CLFlag(true, "enables smart splitting in datatype theory", false));
  flags.addFlag("dt-lazy",
                CLFlag(false, "lazy splitting on datatypes", false));

  return flags;
}

ValidityChecker* ValidityChecker::create(const CLFlags& flags) {
  return new ValidityChecker(flags);
}

ValidityChecker* ValidityChecker::create() {
  return new ValidityChecker(createFlags());
}

Type ValidityChecker::boolType() {
  return d_em->booleanType();
}

Type ValidityChecker::realType() {
  return d_em->realType();
}

Type ValidityChecker::intType() {
  return d_em->integerType();
}

Type ValidityChecker::subrangeType(const Expr& l, const Expr& r) {
  bool noLowerBound = l.getType().isString() && l.getConst<CVC4::String>() == "_NEGINF";
  bool noUpperBound = r.getType().isString() && r.getConst<CVC4::String>() == "_POSINF";
  CompatCheckArgument(noLowerBound || (l.getKind() == CVC4::kind::CONST_RATIONAL && l.getConst<Rational>().isIntegral()), l);
  CompatCheckArgument(noUpperBound || (r.getKind() == CVC4::kind::CONST_RATIONAL && r.getConst<Rational>().isIntegral()), r);
  CVC4::SubrangeBound bl = noLowerBound ? CVC4::SubrangeBound() : CVC4::SubrangeBound(l.getConst<Rational>().getNumerator());
  CVC4::SubrangeBound br = noUpperBound ? CVC4::SubrangeBound() : CVC4::SubrangeBound(r.getConst<Rational>().getNumerator());
  return d_em->mkSubrangeType(CVC4::SubrangeBounds(bl, br));
}

Type ValidityChecker::subtypeType(const Expr& pred, const Expr& witness) {
  Unimplemented("Predicate subtyping not supported by CVC4 yet (sorry!)");
  /*
  if(witness.isNull()) {
    return d_em->mkPredicateSubtype(pred);
  } else {
    return d_em->mkPredicateSubtype(pred, witness);
  }
  */
}

Type ValidityChecker::tupleType(const Type& type0, const Type& type1) {
  vector<CVC4::Type> types;
  types.push_back(type0);
  types.push_back(type1);
  return d_em->mkTupleType(types);
}

Type ValidityChecker::tupleType(const Type& type0, const Type& type1, const Type& type2) {
  vector<CVC4::Type> types;
  types.push_back(type0);
  types.push_back(type1);
  types.push_back(type2);
  return d_em->mkTupleType(types);
}

Type ValidityChecker::tupleType(const std::vector<Type>& types) {
  const vector<CVC4::Type>& v =
    *reinterpret_cast<const vector<CVC4::Type>*>(&types);
  return Type(d_em->mkTupleType(v));
}

Type ValidityChecker::recordType(const std::string& field, const Type& type) {
  std::vector< std::pair<std::string, CVC4::Type> > fields;
  fields.push_back(std::make_pair(field, (const CVC4::Type&) type));
  return d_em->mkRecordType(CVC4::Record(fields));
}

Type ValidityChecker::recordType(const std::string& field0, const Type& type0,
                                 const std::string& field1, const Type& type1) {
  std::vector< std::pair<std::string, CVC4::Type> > fields;
  fields.push_back(std::make_pair(field0, (const CVC4::Type&) type0));
  fields.push_back(std::make_pair(field1, (const CVC4::Type&) type1));
  return d_em->mkRecordType(CVC4::Record(fields));
}

Type ValidityChecker::recordType(const std::string& field0, const Type& type0,
                                 const std::string& field1, const Type& type1,
                                 const std::string& field2, const Type& type2) {
  std::vector< std::pair<std::string, CVC4::Type> > fields;
  fields.push_back(std::make_pair(field0, (const CVC4::Type&) type0));
  fields.push_back(std::make_pair(field1, (const CVC4::Type&) type1));
  fields.push_back(std::make_pair(field2, (const CVC4::Type&) type2));
  return d_em->mkRecordType(CVC4::Record(fields));
}

Type ValidityChecker::recordType(const std::vector<std::string>& fields,
                                 const std::vector<Type>& types) {
  CompatCheckArgument(fields.size() == types.size() && fields.size() > 0,
                      "invalid vector length(s) in recordType()");
  std::vector< std::pair<std::string, CVC4::Type> > fieldSpecs;
  for(unsigned i = 0; i < fields.size(); ++i) {
    fieldSpecs.push_back(std::make_pair(fields[i], (const CVC4::Type&) types[i]));
  }
  return d_em->mkRecordType(CVC4::Record(fieldSpecs));
}

Type ValidityChecker::dataType(const std::string& name,
                               const std::string& constructor,
                               const std::vector<std::string>& selectors,
                               const std::vector<Expr>& types) {
  CompatCheckArgument(selectors.size() == types.size(), types,
                      "expected selectors and types vectors to be of equal"
                      "length");
  vector<string> cv;
  vector< vector<string> > sv;
  vector< vector<Expr> > tv;
  cv.push_back(constructor);
  sv.push_back(selectors);
  tv.push_back(types);
  return dataType(name, cv, sv, tv);
}

Type ValidityChecker::dataType(const std::string& name,
                               const std::vector<std::string>& constructors,
                               const std::vector<std::vector<std::string> >& selectors,
                               const std::vector<std::vector<Expr> >& types) {
  CompatCheckArgument(constructors.size() == selectors.size(), selectors,
                      "Expected constructors and selectors vectors to be of "
                      "equal length.");
  CompatCheckArgument(constructors.size() == types.size(), types,
                      "Expected constructors and types vectors to be of equal "
                      "length.");
  vector<string> nv;
  vector< vector<string> > cv;
  vector< vector< vector<string> > > sv;
  vector< vector< vector<Expr> > > tv;
  nv.push_back(name);
  cv.push_back(constructors);
  sv.push_back(selectors);
  tv.push_back(types);
  vector<Type> dtts;
  dataType(nv, cv, sv, tv, dtts);
  assert(dtts.size() == 1);
  return dtts[0];
}

void ValidityChecker::dataType(const std::vector<std::string>& names,
                               const std::vector<std::vector<std::string> >& constructors,
                               const std::vector<std::vector<std::vector<std::string> > >& selectors,
                               const std::vector<std::vector<std::vector<Expr> > >& types,
                               std::vector<Type>& returnTypes) {

  CompatCheckArgument(names.size() == constructors.size(), constructors,
                      "Expected names and constructors vectors to be of equal "
                      "length.");
  CompatCheckArgument(names.size() == selectors.size(), selectors,
                      "Expected names and selectors vectors to be of equal "
                      "length.");
  CompatCheckArgument(names.size() == types.size(), types,
                      "Expected names and types vectors to be of equal "
                      "length.");
  vector<CVC4::Datatype> dv;

  // Set up the datatype specifications.
  for(unsigned i = 0; i < names.size(); ++i) {
    CVC4::Datatype dt(names[i], false);
    CompatCheckArgument(constructors[i].size() == selectors[i].size(),
                        "Expected sub-vectors in constructors and selectors "
                        "vectors to match in size.");
    CompatCheckArgument(constructors[i].size() == types[i].size(),
                        "Expected sub-vectors in constructors and types "
                        "vectors to match in size.");
    for(unsigned j = 0; j < constructors[i].size(); ++j) {
      CVC4::DatatypeConstructor ctor(constructors[i][j]);
      CompatCheckArgument(selectors[i][j].size() == types[i][j].size(), types,
                          "Expected sub-vectors in selectors and types vectors "
                          "to match in size.");
      for(unsigned k = 0; k < selectors[i][j].size(); ++k) {
        if(types[i][j][k].getType().isString()) {
          CVC4::DatatypeUnresolvedType unresolvedName = 
            types[i][j][k].getConst<CVC4::String>().toString();
          ctor.addArg(selectors[i][j][k], unresolvedName);
        } else {
          ctor.addArg(selectors[i][j][k], exprToType(types[i][j][k]));
        }
      }
      dt.addConstructor(ctor);
    }
    dv.push_back(dt);
  }

  // Make the datatypes.
  vector<CVC4::DatatypeType> dtts = d_em->mkMutualDatatypeTypes(dv);

  // Post-process to register the names of everything with this validity checker.
  // This is necessary for the compatibility layer because cons/sel operations are
  // constructed without appealing explicitly to the Datatype they belong to.
  for(vector<CVC4::DatatypeType>::iterator i = dtts.begin(); i != dtts.end(); ++i) {
    // For each datatype...
    const CVC4::Datatype& dt = (*i).getDatatype();
    // ensure it's well-founded (the check is done here because
    // that's how it is in CVC3)
    CompatCheckArgument(dt.isWellFounded(), "datatype is not well-founded");
    for(CVC4::Datatype::const_iterator j = dt.begin(); j != dt.end(); ++j) {
      // For each constructor, register its name and its selectors names.
      CompatCheckArgument(
          d_constructors.find((*j).getName()) == d_constructors.end(),
          constructors,
          "Cannot have two constructors with the same name in a "
          "ValidityChecker.");
      d_constructors[(*j).getName()] = &dt;
      for(CVC4::DatatypeConstructor::const_iterator k = (*j).begin(); k != (*j).end(); ++k) {
        CompatCheckArgument(
            d_selectors.find((*k).getName()) == d_selectors.end(), selectors,
            "Cannot have two selectors with the same name in a "
            "ValidityChecker.");
        d_selectors[(*k).getName()] = make_pair(&dt, (*j).getName());
      }
    }
  }

  // Copy into the output buffer.
  returnTypes.clear();
  copy(dtts.begin(), dtts.end(), back_inserter(returnTypes));
}

Type ValidityChecker::arrayType(const Type& typeIndex, const Type& typeData) {
  return d_em->mkArrayType(typeIndex, typeData);
}

Type ValidityChecker::bitvecType(int n) {
  CompatCheckArgument(n >= 0, n,
                      "Cannot construct a bitvector type of negative size.");
  return d_em->mkBitVectorType(n);
}

Type ValidityChecker::funType(const Type& typeDom, const Type& typeRan) {
  return d_em->mkFunctionType(typeDom, typeRan);
}

Type ValidityChecker::funType(const std::vector<Type>& typeDom, const Type& typeRan) {
  const vector<CVC4::Type>& dom =
    *reinterpret_cast<const vector<CVC4::Type>*>(&typeDom);
  return Type(d_em->mkFunctionType(dom, typeRan));
}

Type ValidityChecker::createType(const std::string& typeName) {
  return d_em->mkSort(typeName);
}

Type ValidityChecker::createType(const std::string& typeName, const Type& def) {
  d_parserContext->defineType(typeName, def);
  return def;
}

Type ValidityChecker::lookupType(const std::string& typeName) {
  return d_parserContext->getSort(typeName);
}

ExprManager* ValidityChecker::getEM() {
  return d_em;
}

Expr ValidityChecker::varExpr(const std::string& name, const Type& type) {
  return d_parserContext->mkVar(name, type);
}

Expr ValidityChecker::varExpr(const std::string& name, const Type& type,
                              const Expr& def) {
  CompatCheckArgument(def.getType() == type, def, "expected types to match");
  d_parserContext->defineVar(name, def);
  return def;
}

Expr ValidityChecker::lookupVar(const std::string& name, Type* type) {
  return d_parserContext->getVariable(name);
}

Type ValidityChecker::getType(const Expr& e) {
  return d_em->getType(e);
}

Type ValidityChecker::getBaseType(const Expr& e) {
  return getBaseType(e.getType());
}

Type ValidityChecker::getBaseType(const Type& t) {
  return t.getBaseType();
}

Expr ValidityChecker::getTypePred(const Type&t, const Expr& e) {
  // This function appears to be TCC-related---it doesn't just get the pred of a
  // subtype predicate, but returns a predicate describing the type.
  Unimplemented("This CVC3 compatibility function not yet implemented (sorry!)");
}

Expr ValidityChecker::stringExpr(const std::string& str) {
  return d_em->mkConst(CVC4::String(str));
}

Expr ValidityChecker::idExpr(const std::string& name) {
  // represent as a string expr, CVC4 doesn't have id exprs
  return d_em->mkConst(CVC4::String(name));
}

Expr ValidityChecker::listExpr(const std::vector<Expr>& kids) {
  return d_em->mkExpr(CVC4::kind::SEXPR, vector<CVC4::Expr>(kids.begin(), kids.end()));
}

Expr ValidityChecker::listExpr(const Expr& e1) {
  return d_em->mkExpr(CVC4::kind::SEXPR, e1);
}

Expr ValidityChecker::listExpr(const Expr& e1, const Expr& e2) {
  return d_em->mkExpr(CVC4::kind::SEXPR, e1, e2);
}

Expr ValidityChecker::listExpr(const Expr& e1, const Expr& e2, const Expr& e3) {
  return d_em->mkExpr(CVC4::kind::SEXPR, e1, e2, e3);
}

Expr ValidityChecker::listExpr(const std::string& op,
                               const std::vector<Expr>& kids) {
  return d_em->mkExpr(CVC4::kind::SEXPR, d_em->mkConst(CVC4::String(op)), vector<CVC4::Expr>(kids.begin(), kids.end()));
}

Expr ValidityChecker::listExpr(const std::string& op, const Expr& e1) {
  return d_em->mkExpr(CVC4::kind::SEXPR, d_em->mkConst(CVC4::String(op)), e1);
}

Expr ValidityChecker::listExpr(const std::string& op, const Expr& e1,
                               const Expr& e2) {
  return d_em->mkExpr(CVC4::kind::SEXPR, d_em->mkConst(CVC4::String(op)), e1, e2);
}

Expr ValidityChecker::listExpr(const std::string& op, const Expr& e1,
                               const Expr& e2, const Expr& e3) {
  return d_em->mkExpr(CVC4::kind::SEXPR, d_em->mkConst(CVC4::String(op)), e1, e2, e3);
}

void ValidityChecker::printExpr(const Expr& e) {
  printExpr(e, Message());
}

void ValidityChecker::printExpr(const Expr& e, std::ostream& os) {
  CVC4::expr::ExprSetDepth::Scope sd(os, -1);
  CVC4::expr::ExprPrintTypes::Scope pt(os, false);
  CVC4::language::SetLanguage::Scope sl(
      os, d_em->getOptions().getOutputLanguage());
  os << e;
}

Expr ValidityChecker::parseExpr(const Expr& e) {
  return e;
}

Type ValidityChecker::parseType(const Expr& e) {
  Unimplemented("This CVC3 compatibility function not yet implemented (sorry!)");
}

Expr ValidityChecker::importExpr(const Expr& e) {
  if(e.getExprManager() == d_em) {
    return e;
  }

  s_validityCheckers[e.getExprManager()]->d_reverseEmmc.insert(this);
  return e.exportTo(d_em, d_emmc[e.getExprManager()]);
}

Type ValidityChecker::importType(const Type& t) {
  if(t.getExprManager() == d_em) {
    return t;
  }

  s_validityCheckers[t.getExprManager()]->d_reverseEmmc.insert(this);
  return t.exportTo(d_em, d_emmc[t.getExprManager()]);
}

void ValidityChecker::cmdsFromString(const std::string& s, InputLanguage lang) {
  std::stringstream ss(s, std::stringstream::in);
  return loadFile(ss, lang, false);
}

Expr ValidityChecker::exprFromString(const std::string& s, InputLanguage lang) {
  std::stringstream ss;

  if( lang != PRESENTATION_LANG && lang != SMTLIB_V2_LANG ) {
    ss << lang;
    throw Exception("Unsupported language in exprFromString: " + ss.str());
  }

  CVC4::parser::Parser* p = CVC4::parser::ParserBuilder(d_em, "<internal>").withStringInput(s).withInputLanguage(lang).build();
  p->useDeclarationsFrom(d_parserContext);
  Expr e = p->nextExpression();
  if( e.isNull() ) {
    throw CVC4::parser::ParserException("Parser result is null: '" + s + "'");
  }

  delete p;

  return e;
}

Expr ValidityChecker::trueExpr() {
  return d_em->mkConst(true);
}

Expr ValidityChecker::falseExpr() {
  return d_em->mkConst(false);
}

Expr ValidityChecker::notExpr(const Expr& child) {
  return d_em->mkExpr(CVC4::kind::NOT, child);
}

Expr ValidityChecker::andExpr(const Expr& left, const Expr& right) {
  return d_em->mkExpr(CVC4::kind::AND, left, right);
}

Expr ValidityChecker::andExpr(const std::vector<Expr>& children) {
  // AND must have at least 2 children
  CompatCheckArgument(children.size() > 0, children);
  return (children.size() == 1) ? children[0] : Expr(d_em->mkExpr(CVC4::kind::AND, *reinterpret_cast<const vector<CVC4::Expr>*>(&children)));
}

Expr ValidityChecker::orExpr(const Expr& left, const Expr& right) {
  return d_em->mkExpr(CVC4::kind::OR, left, right);
}

Expr ValidityChecker::orExpr(const std::vector<Expr>& children) {
  // OR must have at least 2 children
  CompatCheckArgument(children.size() > 0, children);
  return (children.size() == 1) ? children[0] : Expr(d_em->mkExpr(CVC4::kind::OR, *reinterpret_cast<const vector<CVC4::Expr>*>(&children)));
}

Expr ValidityChecker::impliesExpr(const Expr& hyp, const Expr& conc) {
  return d_em->mkExpr(CVC4::kind::IMPLIES, hyp, conc);
}

Expr ValidityChecker::iffExpr(const Expr& left, const Expr& right) {
  return d_em->mkExpr(CVC4::kind::IFF, left, right);
}

Expr ValidityChecker::eqExpr(const Expr& child0, const Expr& child1) {
  return d_em->mkExpr(CVC4::kind::EQUAL, child0, child1);
}

Expr ValidityChecker::iteExpr(const Expr& ifpart, const Expr& thenpart,
                              const Expr& elsepart) {
  return d_em->mkExpr(CVC4::kind::ITE, ifpart, thenpart, elsepart);
}

Expr ValidityChecker::distinctExpr(const std::vector<Expr>& children) {
  CompatCheckArgument(children.size() > 1, children, "it makes no sense to create a `distinct' expression with only one child");
  const vector<CVC4::Expr>& v =
    *reinterpret_cast<const vector<CVC4::Expr>*>(&children);
  return d_em->mkExpr(CVC4::kind::DISTINCT, v);
}

Op ValidityChecker::createOp(const std::string& name, const Type& type) {
  return d_parserContext->mkVar(name, type);
}

Op ValidityChecker::createOp(const std::string& name, const Type& type,
                             const Expr& def) {
  CompatCheckArgument(def.getType() == type, type,
      "Type mismatch in ValidityChecker::createOp(): `%s' defined to an "
      "expression of type %s but ascribed as type %s", name.c_str(),
      def.getType().toString().c_str(), type.toString().c_str());
  d_parserContext->defineFunction(name, def);
  return def;
}

Op ValidityChecker::lookupOp(const std::string& name, Type* type) {
  Op op = d_parserContext->getFunction(name);
  *type = op.getType();
  return op;
}

Expr ValidityChecker::funExpr(const Op& op, const Expr& child) {
  return d_em->mkExpr(CVC4::kind::APPLY_UF, op, child);
}

Expr ValidityChecker::funExpr(const Op& op, const Expr& left, const Expr& right) {
  return d_em->mkExpr(CVC4::kind::APPLY_UF, op, left, right);
}

Expr ValidityChecker::funExpr(const Op& op, const Expr& child0,
                              const Expr& child1, const Expr& child2) {
  return d_em->mkExpr(CVC4::kind::APPLY_UF, op, child0, child1, child2);
}

Expr ValidityChecker::funExpr(const Op& op, const std::vector<Expr>& children) {
  vector<CVC4::Expr> opkids;
  opkids.push_back(op);
  opkids.insert(opkids.end(), children.begin(), children.end());
  return d_em->mkExpr(CVC4::kind::APPLY_UF, opkids);
}

bool ValidityChecker::addPairToArithOrder(const Expr& smaller, const Expr& bigger) {
  Unimplemented("This CVC3 compatibility function not yet implemented (sorry!)");
}

Expr ValidityChecker::ratExpr(int n, int d) {
  return d_em->mkConst(Rational(n, d));
}

Expr ValidityChecker::ratExpr(const std::string& n, const std::string& d, int base) {
  return d_em->mkConst(Rational(n + '/' + d, base));
}

Expr ValidityChecker::ratExpr(const std::string& n, int base) {
  if(n.find(".") == string::npos) {
    return d_em->mkConst(Rational(n, base));
  } else {
    CompatCheckArgument(base == 10, base, "unsupported base for decimal parsing");
    return d_em->mkConst(Rational::fromDecimal(n));
  }
}

Expr ValidityChecker::uminusExpr(const Expr& child) {
  return d_em->mkExpr(CVC4::kind::UMINUS, child);
}

Expr ValidityChecker::plusExpr(const Expr& left, const Expr& right) {
  return d_em->mkExpr(CVC4::kind::PLUS, left, right);
}

Expr ValidityChecker::plusExpr(const std::vector<Expr>& children) {
  // PLUS must have at least 2 children
  CompatCheckArgument(children.size() > 0, children);
  return (children.size() == 1) ? children[0] : Expr(d_em->mkExpr(CVC4::kind::PLUS, *reinterpret_cast<const vector<CVC4::Expr>*>(&children)));
}

Expr ValidityChecker::minusExpr(const Expr& left, const Expr& right) {
  return d_em->mkExpr(CVC4::kind::MINUS, left, right);
}

Expr ValidityChecker::multExpr(const Expr& left, const Expr& right) {
  return d_em->mkExpr(CVC4::kind::MULT, left, right);
}

Expr ValidityChecker::powExpr(const Expr& x, const Expr& n) {
  return d_em->mkExpr(CVC4::kind::POW, x, n);
}

Expr ValidityChecker::divideExpr(const Expr& numerator,
                                 const Expr& denominator) {
  return d_em->mkExpr(CVC4::kind::DIVISION, numerator, denominator);
}

Expr ValidityChecker::ltExpr(const Expr& left, const Expr& right) {
  return d_em->mkExpr(CVC4::kind::LT, left, right);
}

Expr ValidityChecker::leExpr(const Expr& left, const Expr& right) {
  return d_em->mkExpr(CVC4::kind::LEQ, left, right);
}

Expr ValidityChecker::gtExpr(const Expr& left, const Expr& right) {
  return d_em->mkExpr(CVC4::kind::GT, left, right);
}

Expr ValidityChecker::geExpr(const Expr& left, const Expr& right) {
  return d_em->mkExpr(CVC4::kind::GEQ, left, right);
}

Expr ValidityChecker::recordExpr(const std::string& field, const Expr& expr) {
  CVC4::Type t = recordType(field, expr.getType());
  const CVC4::Datatype& dt = ((CVC4::DatatypeType)t).getDatatype();
  return d_em->mkExpr(CVC4::kind::APPLY_CONSTRUCTOR, dt[0].getConstructor(), expr);
}

Expr ValidityChecker::recordExpr(const std::string& field0, const Expr& expr0,
                                 const std::string& field1, const Expr& expr1) {
  CVC4::Type t = recordType(field0, expr0.getType(),
                            field1, expr1.getType());
  const CVC4::Datatype& dt = ((CVC4::DatatypeType)t).getDatatype();
  return d_em->mkExpr(CVC4::kind::APPLY_CONSTRUCTOR, dt[0].getConstructor(), expr0, expr1);
}

Expr ValidityChecker::recordExpr(const std::string& field0, const Expr& expr0,
                                 const std::string& field1, const Expr& expr1,
                                 const std::string& field2, const Expr& expr2) {
  CVC4::Type t = recordType(field0, expr0.getType(),
                            field1, expr1.getType(),
                            field2, expr2.getType());
  const CVC4::Datatype& dt = ((CVC4::DatatypeType)t).getDatatype();
  return d_em->mkExpr(CVC4::kind::APPLY_CONSTRUCTOR, dt[0].getConstructor(), expr0, expr1, expr2);
}

Expr ValidityChecker::recordExpr(const std::vector<std::string>& fields,
                                 const std::vector<Expr>& exprs) {
  std::vector<Type> types;
  for(unsigned i = 0; i < exprs.size(); ++i) {
    types.push_back(exprs[i].getType());
  }
  CVC4::Type t = recordType(fields, types);
  const CVC4::Datatype& dt = ((CVC4::DatatypeType)t).getDatatype();
  return d_em->mkExpr(CVC4::kind::APPLY_CONSTRUCTOR, dt[0].getConstructor(), *reinterpret_cast<const vector<CVC4::Expr>*>(&exprs));
}

Expr ValidityChecker::recSelectExpr(const Expr& record, const std::string& field) {
  Type t = record.getType();
  const CVC4::Datatype& dt = ((CVC4::DatatypeType)t).getDatatype();
  unsigned index = CVC4::Datatype::indexOf( dt[0].getSelector(field) );
  return d_em->mkExpr(CVC4::kind::APPLY_SELECTOR_TOTAL, dt[0][index].getSelector(), record);
}

Expr ValidityChecker::recUpdateExpr(const Expr& record, const std::string& field,
                                    const Expr& newValue) {
  return d_em->mkExpr(d_em->mkConst(CVC4::RecordUpdate(field)), record, newValue);
}

Expr ValidityChecker::readExpr(const Expr& array, const Expr& index) {
  return d_em->mkExpr(CVC4::kind::SELECT, array, index);
}

Expr ValidityChecker::writeExpr(const Expr& array, const Expr& index,
                                const Expr& newValue) {
  return d_em->mkExpr(CVC4::kind::STORE, array, index, newValue);
}

Expr ValidityChecker::newBVConstExpr(const std::string& s, int base) {
  return d_em->mkConst(CVC4::BitVector(s, base));
}

Expr ValidityChecker::newBVConstExpr(const std::vector<bool>& bits) {
  Integer value = 0;
  for(vector<bool>::const_iterator i = bits.begin(); i != bits.end(); ++i) {
    value *= 2;
    value += *i ? 1 : 0;
  }
  return d_em->mkConst(CVC4::BitVector(bits.size(), value));
}

Expr ValidityChecker::newBVConstExpr(const Rational& r, int len) {
  // implementation based on CVC3's TheoryBitvector::newBVConstExpr()

  CompatCheckArgument(r.getDenominator() == 1, r,
                      "ValidityChecker::newBVConstExpr: "
                      "not an integer: `%s'", r.toString().c_str());
  CompatCheckArgument(len > 0, len, "ValidityChecker::newBVConstExpr: "
                      "len = %d", len);

  string s(r.toString(2));
  size_t strsize = s.size();
  size_t length = len;
  Expr res;
  if(length > 0 && length != strsize) {
    //either (length > strsize) or (length < strsize)
    if(length < strsize) {
      s = s.substr(strsize - length, length);
    } else {
      string zeros("");
      for(size_t i = 0, pad = length - strsize; i < pad; ++i)
	zeros += "0";
      s = zeros + s;
    }
  }

  return newBVConstExpr(s, 2);
}

Expr ValidityChecker::newConcatExpr(const Expr& t1, const Expr& t2) {
  CompatCheckArgument(t1.getType().isBitVector(), t1, "can only concat a bitvector, not a `%s'", t1.getType().toString().c_str());
  CompatCheckArgument(t2.getType().isBitVector(), t2, "can only concat a bitvector, not a `%s'", t2.getType().toString().c_str());
  return d_em->mkExpr(CVC4::kind::BITVECTOR_CONCAT, t1, t2);
}

Expr ValidityChecker::newConcatExpr(const std::vector<Expr>& kids) {
  const vector<CVC4::Expr>& v =
    *reinterpret_cast<const vector<CVC4::Expr>*>(&kids);
  return d_em->mkExpr(CVC4::kind::BITVECTOR_CONCAT, v);
}

Expr ValidityChecker::newBVExtractExpr(const Expr& e, int hi, int low) {
  CompatCheckArgument(e.getType().isBitVector(), e,
                      "can only bvextract from a bitvector, not a `%s'",
                      e.getType().toString().c_str());
  CompatCheckArgument(hi >= low, hi,
                      "extraction [%d:%d] is bad; possibly inverted?", hi, low);
  CompatCheckArgument(low >= 0, low,
                      "extraction [%d:%d] is bad (negative)", hi, low);
  CompatCheckArgument(CVC4::BitVectorType(e.getType()).getSize() > unsigned(hi),
                      hi,
                      "bitvector is of size %u, extraction [%d:%d] is off-the-end",
                      CVC4::BitVectorType(e.getType()).getSize(), hi, low);
  return d_em->mkExpr(CVC4::kind::BITVECTOR_EXTRACT,
                      d_em->mkConst(CVC4::BitVectorExtract(hi, low)), e);
}

Expr ValidityChecker::newBVNegExpr(const Expr& t1) {
  // CVC3's BVNEG => SMT-LIBv2 bvnot
  CompatCheckArgument(t1.getType().isBitVector(), t1,
                      "can only bvneg a bitvector, not a `%s'",
                      t1.getType().toString().c_str());
  return d_em->mkExpr(CVC4::kind::BITVECTOR_NOT, t1);
}

Expr ValidityChecker::newBVAndExpr(const Expr& t1, const Expr& t2) {
  CompatCheckArgument(t1.getType().isBitVector(), t1,
                      "can only bvand a bitvector, not a `%s'",
                      t1.getType().toString().c_str());
  CompatCheckArgument(t2.getType().isBitVector(), t2,
                      "can only bvand a bitvector, not a `%s'",
                      t2.getType().toString().c_str());
  return d_em->mkExpr(CVC4::kind::BITVECTOR_AND, t1, t2);
}

Expr ValidityChecker::newBVAndExpr(const std::vector<Expr>& kids) {
  // BITVECTOR_AND is not N-ary in CVC4
  CompatCheckArgument(kids.size() > 1, kids,
                      "BITVECTOR_AND must have at least 2 children");
  std::vector<Expr>::const_reverse_iterator i = kids.rbegin();
  Expr e = *i++;
  while(i != kids.rend()) {
    e = d_em->mkExpr(CVC4::kind::BITVECTOR_AND, *i++, e);
  }
  return e;
}

Expr ValidityChecker::newBVOrExpr(const Expr& t1, const Expr& t2) {
  CompatCheckArgument(t1.getType().isBitVector(), t1,
                      "can only bvor a bitvector, not a `%s'",
                      t1.getType().toString().c_str());
  CompatCheckArgument(t2.getType().isBitVector(), t2,
                      "can only bvor a bitvector, not a `%s'",
                      t2.getType().toString().c_str());
  return d_em->mkExpr(CVC4::kind::BITVECTOR_OR, t1, t2);
}

Expr ValidityChecker::newBVOrExpr(const std::vector<Expr>& kids) {
  // BITVECTOR_OR is not N-ary in CVC4
  CompatCheckArgument(kids.size() > 1, kids,
                      "BITVECTOR_OR must have at least 2 children");
  std::vector<Expr>::const_reverse_iterator i = kids.rbegin();
  Expr e = *i++;
  while(i != kids.rend()) {
    e = d_em->mkExpr(CVC4::kind::BITVECTOR_OR, *i++, e);
  }
  return e;
}

Expr ValidityChecker::newBVXorExpr(const Expr& t1, const Expr& t2) {
  CompatCheckArgument(t1.getType().isBitVector(), t1,
                      "can only bvxor a bitvector, not a `%s'",
                      t1.getType().toString().c_str());
  CompatCheckArgument(t2.getType().isBitVector(), t2,
                      "can only bvxor a bitvector, not a `%s'",
                      t2.getType().toString().c_str());
  return d_em->mkExpr(CVC4::kind::BITVECTOR_XOR, t1, t2);
}

Expr ValidityChecker::newBVXorExpr(const std::vector<Expr>& kids) {
  // BITVECTOR_XOR is not N-ary in CVC4
  CompatCheckArgument(kids.size() > 1, kids,
                      "BITVECTOR_XOR must have at least 2 children");
  std::vector<Expr>::const_reverse_iterator i = kids.rbegin();
  Expr e = *i++;
  while(i != kids.rend()) {
    e = d_em->mkExpr(CVC4::kind::BITVECTOR_XOR, *i++, e);
  }
  return e;
}

Expr ValidityChecker::newBVXnorExpr(const Expr& t1, const Expr& t2) {
  CompatCheckArgument(t1.getType().isBitVector(), t1,
                      "can only bvxnor a bitvector, not a `%s'",
                      t1.getType().toString().c_str());
  CompatCheckArgument(t2.getType().isBitVector(), t2,
                      "can only bvxnor a bitvector, not a `%s'",
                      t2.getType().toString().c_str());
  return d_em->mkExpr(CVC4::kind::BITVECTOR_XNOR, t1, t2);
}

Expr ValidityChecker::newBVXnorExpr(const std::vector<Expr>& kids) {
  // BITVECTOR_XNOR is not N-ary in CVC4
  CompatCheckArgument(kids.size() > 1, kids,
                      "BITVECTOR_XNOR must have at least 2 children");
  std::vector<Expr>::const_reverse_iterator i = kids.rbegin();
  Expr e = *i++;
  while(i != kids.rend()) {
    e = d_em->mkExpr(CVC4::kind::BITVECTOR_XNOR, *i++, e);
  }
  return e;
}

Expr ValidityChecker::newBVNandExpr(const Expr& t1, const Expr& t2) {
  CompatCheckArgument(t1.getType().isBitVector(), t1,
                      "can only bvnand a bitvector, not a `%s'",
                      t1.getType().toString().c_str());
  CompatCheckArgument(t2.getType().isBitVector(), t2,
                      "can only bvnand a bitvector, not a `%s'",
                      t2.getType().toString().c_str());
  return d_em->mkExpr(CVC4::kind::BITVECTOR_NAND, t1, t2);
}

Expr ValidityChecker::newBVNorExpr(const Expr& t1, const Expr& t2) {
  CompatCheckArgument(t1.getType().isBitVector(), t1,
                      "can only bvnor a bitvector, not a `%s'",
                      t1.getType().toString().c_str());
  CompatCheckArgument(t2.getType().isBitVector(), t2,
                      "can only bvnor a bitvector, not a `%s'",
                      t2.getType().toString().c_str());
  return d_em->mkExpr(CVC4::kind::BITVECTOR_NOR, t1, t2);
}

Expr ValidityChecker::newBVCompExpr(const Expr& t1, const Expr& t2) {
  CompatCheckArgument(t1.getType().isBitVector(), t1, "can only bvcomp a bitvector, not a `%s'", t1.getType().toString().c_str());
  CompatCheckArgument(t2.getType().isBitVector(), t2, "can only bvcomp a bitvector, not a `%s'", t2.getType().toString().c_str());
  return d_em->mkExpr(CVC4::kind::BITVECTOR_COMP, t1, t2);
}

Expr ValidityChecker::newBVLTExpr(const Expr& t1, const Expr& t2) {
  CompatCheckArgument(t1.getType().isBitVector(), t1, "can only bvlt a bitvector, not a `%s'", t1.getType().toString().c_str());
  CompatCheckArgument(t2.getType().isBitVector(), t2, "can only bvlt a bitvector, not a `%s'", t2.getType().toString().c_str());
  return d_em->mkExpr(CVC4::kind::BITVECTOR_ULT, t1, t2);
}

Expr ValidityChecker::newBVLEExpr(const Expr& t1, const Expr& t2) {
  CompatCheckArgument(t1.getType().isBitVector(), t1, "can only bvle a bitvector, not a `%s'", t1.getType().toString().c_str());
  CompatCheckArgument(t2.getType().isBitVector(), t2, "can only bvle a bitvector, not a `%s'", t2.getType().toString().c_str());
  return d_em->mkExpr(CVC4::kind::BITVECTOR_ULE, t1, t2);
}

Expr ValidityChecker::newBVSLTExpr(const Expr& t1, const Expr& t2) {
  CompatCheckArgument(t1.getType().isBitVector(), t1, "can only bvslt a bitvector, not a `%s'", t1.getType().toString().c_str());
  CompatCheckArgument(t2.getType().isBitVector(), t2, "can only bvslt a bitvector, not a `%s'", t2.getType().toString().c_str());
  return d_em->mkExpr(CVC4::kind::BITVECTOR_SLT, t1, t2);
}

Expr ValidityChecker::newBVSLEExpr(const Expr& t1, const Expr& t2) {
  CompatCheckArgument(t1.getType().isBitVector(), t1, "can only bvsle a bitvector, not a `%s'", t1.getType().toString().c_str());
  CompatCheckArgument(t2.getType().isBitVector(), t2, "can only bvsle a bitvector, not a `%s'", t2.getType().toString().c_str());
  return d_em->mkExpr(CVC4::kind::BITVECTOR_SLE, t1, t2);
}

Expr ValidityChecker::newSXExpr(const Expr& t1, int len) {
  CompatCheckArgument(t1.getType().isBitVector(), t1, "can only sx a bitvector, not a `%s'", t1.getType().toString().c_str());
  CompatCheckArgument(len >= 0, len, "must sx by a positive integer");
  CompatCheckArgument(unsigned(len) >= CVC4::BitVectorType(t1.getType()).getSize(), len, "cannot sx by something smaller than the bitvector (%d < %u)", len, CVC4::BitVectorType(t1.getType()).getSize());
  return d_em->mkExpr(CVC4::kind::BITVECTOR_SIGN_EXTEND,
                     d_em->mkConst(CVC4::BitVectorSignExtend(len)), t1);
}

Expr ValidityChecker::newBVUminusExpr(const Expr& t1) {
  // CVC3's BVUMINUS => SMT-LIBv2 bvneg
  CompatCheckArgument(t1.getType().isBitVector(), t1, "can only bvuminus a bitvector, not a `%s'", t1.getType().toString().c_str());
  return d_em->mkExpr(CVC4::kind::BITVECTOR_NEG, t1);
}

Expr ValidityChecker::newBVSubExpr(const Expr& t1, const Expr& t2) {
  CompatCheckArgument(t1.getType().isBitVector(), t1, "can only bvsub a bitvector, not a `%s'", t1.getType().toString().c_str());
  CompatCheckArgument(t2.getType().isBitVector(), t2, "can only bvsub by a bitvector, not a `%s'", t2.getType().toString().c_str());
  return d_em->mkExpr(CVC4::kind::BITVECTOR_SUB, t1, t2);
}

// Copied from CVC3's bitvector theory: makes bitvector expression "e"
// into "len" bits, by zero-padding, or extracting least-significant bits.
Expr ValidityChecker::bvpad(int len, const Expr& e) {
  CompatCheckArgument(len >= 0, len,
                "padding length must be a non-negative integer, not %d", len);
  CompatCheckArgument(e.getType().isBitVector(), e,
                "input to bitvector operation must be a bitvector");

  unsigned size = CVC4::BitVectorType(e.getType()).getSize();
  Expr res;
  if(size == len) {
    res = e;
  } else if(len < size) {
    res = d_em->mkExpr(d_em->mkConst(CVC4::BitVectorExtract(len - 1, 0)), e);
  } else {
    // size < len
    Expr zero = d_em->mkConst(CVC4::BitVector(len - size, 0u));
    res = d_em->mkExpr(CVC4::kind::BITVECTOR_CONCAT, zero, e);
  }
  return res;
}

Expr ValidityChecker::newBVPlusExpr(int numbits, const std::vector<Expr>& kids) {
  // BITVECTOR_PLUS is not N-ary in CVC4
  CompatCheckArgument(kids.size() > 1, kids, "BITVECTOR_PLUS must have at least 2 children");
  std::vector<Expr>::const_reverse_iterator i = kids.rbegin();
  Expr e = *i++;
  while(i != kids.rend()) {
    e = d_em->mkExpr(CVC4::kind::BITVECTOR_PLUS, bvpad(numbits, *i++), e);
  }
  unsigned size = CVC4::BitVectorType(e.getType()).getSize();
  CompatCheckArgument(unsigned(numbits) == size, numbits,
                "argument must match computed size of bitvector sum: "
                "passed size == %u, computed size == %u", numbits, size);
  return e;
}

Expr ValidityChecker::newBVPlusExpr(int numbits, const Expr& t1, const Expr& t2) {
  CompatCheckArgument(t1.getType().isBitVector(), t1, "can only bvplus a bitvector, not a `%s'", t1.getType().toString().c_str());
  CompatCheckArgument(t2.getType().isBitVector(), t2, "can only bvplus a bitvector, not a `%s'", t2.getType().toString().c_str());
  Expr e = d_em->mkExpr(CVC4::kind::BITVECTOR_PLUS, bvpad(numbits, t1), bvpad(numbits, t2));
  unsigned size = CVC4::BitVectorType(e.getType()).getSize();
  CompatCheckArgument(unsigned(numbits) == size, numbits,
                "argument must match computed size of bitvector sum: "
                "passed size == %u, computed size == %u", numbits, size);
  return e;
}

Expr ValidityChecker::newBVMultExpr(int numbits, const Expr& t1, const Expr& t2) {
  CompatCheckArgument(t1.getType().isBitVector(), t1, "can only bvmult a bitvector, not a `%s'", t1.getType().toString().c_str());
  CompatCheckArgument(t2.getType().isBitVector(), t2, "can only bvmult by a bitvector, not a `%s'", t2.getType().toString().c_str());
  Expr e = d_em->mkExpr(CVC4::kind::BITVECTOR_MULT, bvpad(numbits, t1), bvpad(numbits, t2));
  unsigned size = CVC4::BitVectorType(e.getType()).getSize();
  CompatCheckArgument(unsigned(numbits) == size, numbits,
                "argument must match computed size of bitvector product: "
                "passed size == %u, computed size == %u", numbits, size);
  return e;
}

Expr ValidityChecker::newBVUDivExpr(const Expr& t1, const Expr& t2) {
  CompatCheckArgument(t1.getType().isBitVector(), t1, "can only bvudiv a bitvector, not a `%s'", t1.getType().toString().c_str());
  CompatCheckArgument(t2.getType().isBitVector(), t2, "can only bvudiv by a bitvector, not a `%s'", t2.getType().toString().c_str());
  return d_em->mkExpr(CVC4::kind::BITVECTOR_UDIV, t1, t2);
}

Expr ValidityChecker::newBVURemExpr(const Expr& t1, const Expr& t2) {
  CompatCheckArgument(t1.getType().isBitVector(), t1, "can only bvurem a bitvector, not a `%s'", t1.getType().toString().c_str());
  CompatCheckArgument(t2.getType().isBitVector(), t2, "can only bvurem by a bitvector, not a `%s'", t2.getType().toString().c_str());
  return d_em->mkExpr(CVC4::kind::BITVECTOR_UREM, t1, t2);
}

Expr ValidityChecker::newBVSDivExpr(const Expr& t1, const Expr& t2) {
  CompatCheckArgument(t1.getType().isBitVector(), t1, "can only bvsdiv a bitvector, not a `%s'", t1.getType().toString().c_str());
  CompatCheckArgument(t2.getType().isBitVector(), t2, "can only bvsdiv by a bitvector, not a `%s'", t2.getType().toString().c_str());
  return d_em->mkExpr(CVC4::kind::BITVECTOR_SDIV, t1, t2);
}

Expr ValidityChecker::newBVSRemExpr(const Expr& t1, const Expr& t2) {
  CompatCheckArgument(t1.getType().isBitVector(), t1, "can only bvsrem a bitvector, not a `%s'", t1.getType().toString().c_str());
  CompatCheckArgument(t2.getType().isBitVector(), t2, "can only bvsrem by a bitvector, not a `%s'", t2.getType().toString().c_str());
  return d_em->mkExpr(CVC4::kind::BITVECTOR_SREM, t1, t2);
}

Expr ValidityChecker::newBVSModExpr(const Expr& t1, const Expr& t2) {
  CompatCheckArgument(t1.getType().isBitVector(), t1, "can only bvsmod a bitvector, not a `%s'", t1.getType().toString().c_str());
  CompatCheckArgument(t2.getType().isBitVector(), t2, "can only bvsmod by a bitvector, not a `%s'", t2.getType().toString().c_str());
  return d_em->mkExpr(CVC4::kind::BITVECTOR_SMOD, t1, t2);
}

Expr ValidityChecker::newFixedLeftShiftExpr(const Expr& t1, int r) {
  CompatCheckArgument(t1.getType().isBitVector(), t1, "can only left-shift a bitvector, not a `%s'", t1.getType().toString().c_str());
  CompatCheckArgument(r >= 0, r, "left shift amount must be >= 0 (you passed %d)", r);
  // Defined in:
  // http://www.cs.nyu.edu/acsys/cvc3/doc/user_doc.html#user_doc_pres_lang_expr_bit
  return d_em->mkExpr(CVC4::kind::BITVECTOR_CONCAT, t1, d_em->mkConst(CVC4::BitVector(r)));
}

Expr ValidityChecker::newFixedConstWidthLeftShiftExpr(const Expr& t1, int r) {
  CompatCheckArgument(t1.getType().isBitVector(), t1, "can only right-shift a bitvector, not a `%s'", t1.getType().toString().c_str());
  CompatCheckArgument(r >= 0, r, "const-width left shift amount must be >= 0 (you passed %d)", r);
  // just turn it into a BVSHL
  return d_em->mkExpr(CVC4::kind::BITVECTOR_SHL, t1, d_em->mkConst(CVC4::BitVector(CVC4::BitVectorType(t1.getType()).getSize(), unsigned(r))));
}

Expr ValidityChecker::newFixedRightShiftExpr(const Expr& t1, int r) {
  CompatCheckArgument(t1.getType().isBitVector(), t1, "can only right-shift a bitvector, not a `%s'", t1.getType().toString().c_str());
  CompatCheckArgument(r >= 0, r, "right shift amount must be >= 0 (you passed %d)", r);
  // Defined in:
  // http://www.cs.nyu.edu/acsys/cvc3/doc/user_doc.html#user_doc_pres_lang_expr_bit
  // Should be equivalent to a BVLSHR; just turn it into that.
  return d_em->mkExpr(CVC4::kind::BITVECTOR_LSHR, t1, d_em->mkConst(CVC4::BitVector(CVC4::BitVectorType(t1.getType()).getSize(), unsigned(r))));
}

Expr ValidityChecker::newBVSHL(const Expr& t1, const Expr& t2) {
  CompatCheckArgument(t1.getType().isBitVector(), t1, "can only right-shift a bitvector, not a `%s'", t1.getType().toString().c_str());
  CompatCheckArgument(t2.getType().isBitVector(), t2, "can only right-shift by a bitvector, not a `%s'", t2.getType().toString().c_str());
  return d_em->mkExpr(CVC4::kind::BITVECTOR_SHL, t1, t2);
}

Expr ValidityChecker::newBVLSHR(const Expr& t1, const Expr& t2) {
  CompatCheckArgument(t1.getType().isBitVector(), t1, "can only right-shift a bitvector, not a `%s'", t1.getType().toString().c_str());
  CompatCheckArgument(t2.getType().isBitVector(), t2, "can only right-shift by a bitvector, not a `%s'", t2.getType().toString().c_str());
  return d_em->mkExpr(CVC4::kind::BITVECTOR_LSHR, t1, t2);
}

Expr ValidityChecker::newBVASHR(const Expr& t1, const Expr& t2) {
  CompatCheckArgument(t1.getType().isBitVector(), t1, "can only right-shift a bitvector, not a `%s'", t1.getType().toString().c_str());
  CompatCheckArgument(t2.getType().isBitVector(), t2, "can only right-shift by a bitvector, not a `%s'", t2.getType().toString().c_str());
  return d_em->mkExpr(CVC4::kind::BITVECTOR_ASHR, t1, t2);
}

Rational ValidityChecker::computeBVConst(const Expr& e) {
  Unimplemented("This CVC3 compatibility function not yet implemented (sorry!)");
}

Expr ValidityChecker::tupleExpr(const std::vector<Expr>& exprs) {
  std::vector< Type > types;
  std::vector<CVC4::Expr> v;
  for( unsigned i=0; i<exprs.size(); i++ ){
    types.push_back( exprs[i].getType() );  
    v.push_back( exprs[i] );
  }
  Type t = tupleType( types );
  const CVC4::Datatype& dt = ((CVC4::DatatypeType)t).getDatatype();
  v.insert( v.begin(), dt[0].getConstructor() );
  return d_em->mkExpr(CVC4::kind::APPLY_CONSTRUCTOR, v);
}

Expr ValidityChecker::tupleSelectExpr(const Expr& tuple, int index) {
  CompatCheckArgument(index >= 0 && index < ((CVC4::DatatypeType)tuple.getType()).getTupleLength(),
                      "invalid index in tuple select");
  const CVC4::Datatype& dt = ((CVC4::DatatypeType)tuple.getType()).getDatatype();
  return d_em->mkExpr(CVC4::kind::APPLY_SELECTOR_TOTAL, dt[0][index].getSelector(), tuple);
}

Expr ValidityChecker::tupleUpdateExpr(const Expr& tuple, int index,
                                      const Expr& newValue) {
  CompatCheckArgument(index >= 0 && index < tuple.getNumChildren(),
                      "invalid index in tuple update");
  return d_em->mkExpr(d_em->mkConst(CVC4::TupleUpdate(index)), tuple, newValue);
}

Expr ValidityChecker::datatypeConsExpr(const std::string& constructor, const std::vector<Expr>& args) {
  ConstructorMap::const_iterator i = d_constructors.find(constructor);
  CompatCheckArgument(i != d_constructors.end(), constructor, "no such constructor");
  const CVC4::Datatype& dt = *(*i).second;
  const CVC4::DatatypeConstructor& ctor = dt[constructor];
  CompatCheckArgument(ctor.getNumArgs() == args.size(), args, "arity mismatch in constructor application");
  return d_em->mkExpr(CVC4::kind::APPLY_CONSTRUCTOR, ctor.getConstructor(), vector<CVC4::Expr>(args.begin(), args.end()));
}

Expr ValidityChecker::datatypeSelExpr(const std::string& selector, const Expr& arg) {
  SelectorMap::const_iterator i = d_selectors.find(selector);
  CompatCheckArgument(i != d_selectors.end(), selector, "no such selector");
  const CVC4::Datatype& dt = *(*i).second.first;
  string constructor = (*i).second.second;
  const CVC4::DatatypeConstructor& ctor = dt[constructor];
  return d_em->mkExpr(CVC4::kind::APPLY_SELECTOR, ctor.getSelector(selector), arg);
}

Expr ValidityChecker::datatypeTestExpr(const std::string& constructor, const Expr& arg) {
  ConstructorMap::const_iterator i = d_constructors.find(constructor);
  CompatCheckArgument(i != d_constructors.end(), constructor, "no such constructor");
  const CVC4::Datatype& dt = *(*i).second;
  const CVC4::DatatypeConstructor& ctor = dt[constructor];
  return d_em->mkExpr(CVC4::kind::APPLY_TESTER, ctor.getTester(), arg);
}

Expr ValidityChecker::boundVarExpr(const std::string& name, const std::string& uid,
                                   const Type& type) {
  return d_em->mkBoundVar(name, type);
}

Expr ValidityChecker::forallExpr(const std::vector<Expr>& vars, const Expr& body) {
  Expr boundVarList = d_em->mkExpr(CVC4::kind::BOUND_VAR_LIST, *reinterpret_cast<const std::vector<CVC4::Expr>*>(&vars));
  return d_em->mkExpr(CVC4::kind::FORALL, boundVarList, body);
}

Expr ValidityChecker::forallExpr(const std::vector<Expr>& vars, const Expr& body,
                                 const Expr& trigger) {
  // trigger
  Expr boundVarList = d_em->mkExpr(CVC4::kind::BOUND_VAR_LIST, *reinterpret_cast<const std::vector<CVC4::Expr>*>(&vars));
  Expr triggerList = d_em->mkExpr(CVC4::kind::INST_PATTERN_LIST, d_em->mkExpr(CVC4::kind::INST_PATTERN, trigger));
  return d_em->mkExpr(CVC4::kind::FORALL, boundVarList, body, triggerList);
}

Expr ValidityChecker::forallExpr(const std::vector<Expr>& vars, const Expr& body,
                                 const std::vector<Expr>& triggers) {
  // set of triggers
  Expr boundVarList = d_em->mkExpr(CVC4::kind::BOUND_VAR_LIST, *reinterpret_cast<const std::vector<CVC4::Expr>*>(&vars));
  std::vector<CVC4::Expr> pats;
  for(std::vector<Expr>::const_iterator i = triggers.begin(); i != triggers.end(); ++i) {
    pats.push_back(d_em->mkExpr(CVC4::kind::INST_PATTERN, *i));
  }
  Expr triggerList = d_em->mkExpr(CVC4::kind::INST_PATTERN_LIST, pats);
  return d_em->mkExpr(CVC4::kind::FORALL, boundVarList, body, triggerList);
}

Expr ValidityChecker::forallExpr(const std::vector<Expr>& vars, const Expr& body,
                                 const std::vector<std::vector<Expr> >& triggers) {
  // set of multi-triggers
  Expr boundVarList = d_em->mkExpr(CVC4::kind::BOUND_VAR_LIST, *reinterpret_cast<const std::vector<CVC4::Expr>*>(&vars));
  std::vector<CVC4::Expr> pats;
  for(std::vector< std::vector<Expr> >::const_iterator i = triggers.begin(); i != triggers.end(); ++i) {
    pats.push_back(d_em->mkExpr(CVC4::kind::INST_PATTERN, *reinterpret_cast<const std::vector<CVC4::Expr>*>(&*i)));
  }
  Expr triggerList = d_em->mkExpr(CVC4::kind::INST_PATTERN_LIST, pats);
  return d_em->mkExpr(CVC4::kind::FORALL, boundVarList, body, triggerList);
}

void ValidityChecker::setTriggers(const Expr& e, const std::vector<std::vector<Expr> > & triggers) {
  Unimplemented("This CVC3 compatibility function not yet implemented (sorry!)");
}

void ValidityChecker::setTriggers(const Expr& e, const std::vector<Expr>& triggers) {
  Unimplemented("This CVC3 compatibility function not yet implemented (sorry!)");
}

void ValidityChecker::setTrigger(const Expr& e, const Expr& trigger) {
  Unimplemented("This CVC3 compatibility function not yet implemented (sorry!)");
}

void ValidityChecker::setMultiTrigger(const Expr& e, const std::vector<Expr>& multiTrigger) {
  Unimplemented("This CVC3 compatibility function not yet implemented (sorry!)");
}

Expr ValidityChecker::existsExpr(const std::vector<Expr>& vars, const Expr& body) {
  Expr boundVarList = d_em->mkExpr(CVC4::kind::BOUND_VAR_LIST, *reinterpret_cast<const std::vector<CVC4::Expr>*>(&vars));
  return d_em->mkExpr(CVC4::kind::EXISTS, boundVarList, body);
}

Op ValidityChecker::lambdaExpr(const std::vector<Expr>& vars, const Expr& body) {
  Unimplemented("Lambda expressions not supported by CVC4 yet (sorry!)");
}

Op ValidityChecker::transClosure(const Op& op) {
  Unimplemented("This CVC3 compatibility function not yet implemented (sorry!)");
}

Expr ValidityChecker::simulateExpr(const Expr& f, const Expr& s0,
                                   const std::vector<Expr>& inputs,
                                   const Expr& n) {
  Unimplemented("This CVC3 compatibility function not yet implemented (sorry!)");
}

void ValidityChecker::setResourceLimit(unsigned limit) {
  // Set a resource limit for CVC4, cumulative (rather than
  // per-query), starting from now.
  d_smt->setResourceLimit(limit, true);
}

void ValidityChecker::setTimeLimit(unsigned limit) {
  // Set a time limit for CVC4, cumulative (rather than per-query),
  // starting from now.  Note that CVC3 uses tenths of a second,
  // while CVC4 uses milliseconds.
  d_smt->setTimeLimit(limit * 100, true);
}

void ValidityChecker::assertFormula(const Expr& e) {
  d_smt->assertFormula(e);
}

void ValidityChecker::registerAtom(const Expr& e) {
  Unimplemented("This CVC3 compatibility function not yet implemented (sorry!)");
}

Expr ValidityChecker::getImpliedLiteral() {
  Unimplemented("This CVC3 compatibility function not yet implemented (sorry!)");
}

Expr ValidityChecker::simplify(const Expr& e) {
  return d_smt->simplify(e);
}

static QueryResult cvc4resultToCvc3result(CVC4::Result r) {
  switch(r.isSat()) {
  case CVC4::Result::SAT:
    return SATISFIABLE;
  case CVC4::Result::UNSAT:
    return UNSATISFIABLE;
  default:
    ;
  }

  switch(r.isValid()) {
  case CVC4::Result::VALID:
    return VALID;
  case CVC4::Result::INVALID:
    return INVALID;
  default:
    return UNKNOWN;
  }
}

QueryResult ValidityChecker::query(const Expr& e) {
  return cvc4resultToCvc3result(d_smt->query(e));
}

QueryResult ValidityChecker::checkUnsat(const Expr& e) {
  return cvc4resultToCvc3result(d_smt->checkSat(e));
}

QueryResult ValidityChecker::checkContinue() {
  Unimplemented("This CVC3 compatibility function not yet implemented (sorry!)");
}

QueryResult ValidityChecker::restart(const Expr& e) {
  Unimplemented("This CVC3 compatibility function not yet implemented (sorry!)");
}

void ValidityChecker::returnFromCheck() {
  // CVC4 has this behavior by default
}

void ValidityChecker::getUserAssumptions(std::vector<Expr>& assumptions) {
  CompatCheckArgument(assumptions.empty(), assumptions, "assumptions arg must be empty");
  vector<CVC4::Expr> v = d_smt->getAssertions();
  assumptions.swap(*reinterpret_cast<vector<Expr>*>(&v));
}

void ValidityChecker::getInternalAssumptions(std::vector<Expr>& assumptions) {
  Unimplemented("This CVC3 compatibility function not yet implemented (sorry!)");
}

void ValidityChecker::getAssumptions(std::vector<Expr>& assumptions) {
  Unimplemented("This CVC3 compatibility function not yet implemented (sorry!)");
}

void ValidityChecker::getAssumptionsUsed(std::vector<Expr>& assumptions) {
  Unimplemented("This CVC3 compatibility function not yet implemented (sorry!)");
}

Expr ValidityChecker::getProofQuery() {
  Unimplemented("This CVC3 compatibility function not yet implemented (sorry!)");
}

void ValidityChecker::getCounterExample(std::vector<Expr>& assumptions,
                                        bool inOrder) {
  Unimplemented("This CVC3 compatibility function not yet implemented (sorry!)");
}

void ValidityChecker::getConcreteModel(ExprMap<Expr>& m) {
  Unimplemented("This CVC3 compatibility function not yet implemented (sorry!)");
}

QueryResult ValidityChecker::tryModelGeneration() {
  Unimplemented("This CVC3 compatibility function not yet implemented (sorry!)");
}

FormulaValue ValidityChecker::value(const Expr& e) {
  CompatCheckArgument(e.getType() == d_em->booleanType(), e, "argument must be a formula");
  try {
    return d_smt->getValue(e).getConst<bool>() ? TRUE_VAL : FALSE_VAL;
  } catch(CVC4::Exception& e) {
    return UNKNOWN_VAL;
  }
}

Expr ValidityChecker::getValue(const Expr& e) {
  try {
    return d_smt->getValue(e);
  } catch(CVC4::ModalException& e) {
    // by contract, we return null expr
    return Expr();
  }
}

bool ValidityChecker::inconsistent(std::vector<Expr>& assumptions) {
  CompatCheckArgument(assumptions.empty(), assumptions, "assumptions vector should be empty on entry");
  if(d_smt->checkSat() == CVC4::Result::UNSAT) {
    // supposed to be a minimal set, but CVC4 doesn't support that
    d_smt->getAssertions().swap(*reinterpret_cast<std::vector<CVC4::Expr>*>(&assumptions));
    return true;
  }
  return false;
}

bool ValidityChecker::inconsistent() {
  return d_smt->checkSat() == CVC4::Result::UNSAT;
}

bool ValidityChecker::incomplete() {
  Unimplemented("This CVC3 compatibility function not yet implemented (sorry!)");
}

bool ValidityChecker::incomplete(std::vector<std::string>& reasons) {
  Unimplemented("This CVC3 compatibility function not yet implemented (sorry!)");
}

Proof ValidityChecker::getProof() {
  Unimplemented("This CVC3 compatibility function not yet implemented (sorry!)");
}

Expr ValidityChecker::getTCC() {
  Unimplemented("This CVC3 compatibility function not yet implemented (sorry!)");
}

void ValidityChecker::getAssumptionsTCC(std::vector<Expr>& assumptions) {
  Unimplemented("This CVC3 compatibility function not yet implemented (sorry!)");
}

Proof ValidityChecker::getProofTCC() {
  Unimplemented("This CVC3 compatibility function not yet implemented (sorry!)");
}

Expr ValidityChecker::getClosure() {
  Unimplemented("This CVC3 compatibility function not yet implemented (sorry!)");
}

Proof ValidityChecker::getProofClosure() {
  Unimplemented("This CVC3 compatibility function not yet implemented (sorry!)");
}

int ValidityChecker::stackLevel() {
  return d_stackLevel;
}

void ValidityChecker::push() {
  ++d_stackLevel;
  d_smt->push();
}

void ValidityChecker::pop() {
  d_smt->pop();
  --d_stackLevel;
}

void ValidityChecker::popto(int stackLevel) {
  CompatCheckArgument(stackLevel >= 0, stackLevel,
                      "Cannot pop to a negative stack level %d", stackLevel);
  CompatCheckArgument(unsigned(stackLevel) <= d_stackLevel, stackLevel,
                      "Cannot pop to a stack level higher than the current one!  "
                      "At stack level %u, user requested stack level %d",
                      d_stackLevel, stackLevel);
  while(unsigned(stackLevel) < d_stackLevel) {
    pop();
  }
}

int ValidityChecker::scopeLevel() {
  return d_parserContext->scopeLevel();
}

void ValidityChecker::pushScope() {
  d_parserContext->pushScope();
}

void ValidityChecker::popScope() {
  d_parserContext->popScope();
}

void ValidityChecker::poptoScope(int scopeLevel) {
  CompatCheckArgument(scopeLevel >= 0, scopeLevel,
                      "Cannot pop to a negative scope level %d", scopeLevel);
  CompatCheckArgument(unsigned(scopeLevel) <= d_parserContext->scopeLevel(),
                      scopeLevel,
                      "Cannot pop to a scope level higher than the current one!  "
                      "At scope level %u, user requested scope level %d",
                      d_parserContext->scopeLevel(), scopeLevel);
  while(unsigned(scopeLevel) < d_parserContext->scopeLevel()) {
    popScope();
  }
}

Context* ValidityChecker::getCurrentContext() {
  Unimplemented("Contexts are not part of the public interface of CVC4");
}

void ValidityChecker::reset() {
  // reset everything, forget everything
  d_smt->reset();
  delete d_parserContext;
  d_parserContext = CVC4::parser::ParserBuilder(d_em, "<internal>").withInputLanguage(CVC4::language::input::LANG_CVC4).withStringInput("").build();
  s_typeToExpr.clear();
  s_exprToType.clear();
}

void ValidityChecker::logAnnotation(const Expr& annot) {
  Unimplemented("This CVC3 compatibility function not yet implemented (sorry!)");
}

static void doCommands(CVC4::parser::Parser* parser, CVC4::SmtEngine* smt, CVC4::Options& opts) {
  while(CVC4::Command* cmd = parser->nextCommand()) {
    if(opts.getVerbosity() >= 0) {
      cmd->invoke(smt, *opts.getOut());
    } else {
      cmd->invoke(smt);
    }
    delete cmd;
  }
}

void ValidityChecker::loadFile(const std::string& fileName,
                               InputLanguage lang,
                               bool interactive,
                               bool calledFromParser) {
  CVC4::Options opts;
  opts.copyValues(d_em->getOptions());
  stringstream langss;
  langss << lang;
  d_smt->setOption("input-language", CVC4::SExpr(langss.str()));
  d_smt->setOption("interactive-mode", CVC4::SExpr(interactive ? true : false));
  CVC4::parser::ParserBuilder parserBuilder(d_em, fileName, opts);
  CVC4::parser::Parser* p = parserBuilder.build();
  p->useDeclarationsFrom(d_parserContext);
  doCommands(p, d_smt, opts);
  delete p;
}

void ValidityChecker::loadFile(std::istream& is,
                               InputLanguage lang,
                               bool interactive) {
  CVC4::Options opts;
  opts.copyValues(d_em->getOptions());

  stringstream langss;
  langss << lang;
  d_smt->setOption("input-language", CVC4::SExpr(langss.str()));
  d_smt->setOption("interactive-mode", CVC4::SExpr(interactive ? true : false));
  CVC4::parser::ParserBuilder parserBuilder(d_em, "[stream]", opts);
  CVC4::parser::Parser* p = parserBuilder.withStreamInput(is).build();
  d_parserContext = p;
  p->useDeclarationsFrom(d_parserContext);
  doCommands(p, d_smt, opts);
  delete p;
}

Statistics ValidityChecker::getStatistics() {
  return d_smt->getStatistics();
}

void ValidityChecker::printStatistics() {
  d_smt->getStatistics().flushInformation(Message.getStream());
}

int compare(const Expr& e1, const Expr& e2) {
  // Quick equality check (operator== is implemented independently
  // and more efficiently)
  if(e1 == e2) return 0;

  if(e1.isNull()) return -1;
  if(e2.isNull()) return 1;

  // Both are non-Null.  Check for constant
  bool e1c = e1.isConstant();
  if (e1c != e2.isConstant()) {
    return e1c ? -1 : 1;
  }

  // Compare the indices
  return (e1.getIndex() < e2.getIndex())? -1 : 1;
}

}/* CVC3 namespace */
