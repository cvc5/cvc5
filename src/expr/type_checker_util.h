/*********************                                                        */
/*! \file type_checker_util.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andres Noetzli
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Templates for simple type rules
 **
 ** This file defines templates for simple type rules. If a kind has the a
 ** type rule where each argument matches exactly a specific sort, these
 ** templates can be used to define typechecks without writing dedicated classes
 ** for them.
 **/

#include "cvc4_private.h"

#include "expr/kind.h"
#include "expr/node.h"
#include "expr/node_manager.h"
#include "expr/type_node.h"

namespace CVC4 {
namespace expr {

/** Type check returns the builtin operator sort */
struct RBuiltinOperator
{
  static TypeNode mkType(NodeManager* nm) { return nm->builtinOperatorType(); }
};

/** Type check returns the Boolean sort */
struct RBool
{
  static TypeNode mkType(NodeManager* nm) { return nm->booleanType(); }
};

/** Type check returns the integer sort */
struct RInteger
{
  static TypeNode mkType(NodeManager* nm) { return nm->integerType(); }
};

/** Type check returns the real sort */
struct RReal
{
  static TypeNode mkType(NodeManager* nm) { return nm->realType(); }
};

/** Type check returns the regexp sort */
struct RRegExp
{
  static TypeNode mkType(NodeManager* nm) { return nm->regExpType(); }
};

/** Type check returns the string sort */
struct RString
{
  static TypeNode mkType(NodeManager* nm) { return nm->stringType(); }
};

/** Argument does not exist */
struct ANone
{
  static bool checkArg(TNode n, size_t arg)
  {
    Assert(arg >= n.getNumChildren());
    return true;
  }
  constexpr static const char* typeName = "<none>";
};

/** Argument is optional */
template<class A>
struct AOptional
{
  static bool checkArg(TNode n, size_t arg)
  {
    if (arg < n.getNumChildren()) {
      return A::checkArg(n, arg);
    }
    return true;
  }
  constexpr static const char* typeName = A::typeName;
};

/** Argument is an integer */
struct AInteger
{
  static bool checkArg(TNode n, size_t arg)
  {
    TypeNode t = n[arg].getType(true);
    return t.isInteger();
  }
  constexpr static const char* typeName = "integer";
};

/** Argument is a real */
struct AReal
{
  static bool checkArg(TNode n, size_t arg)
  {
    TypeNode t = n[arg].getType(true);
    return t.isReal();
  }
  constexpr static const char* typeName = "real";
};

/** Argument is a regexp */
struct ARegExp
{
  static bool checkArg(TNode n, size_t arg)
  {
    TypeNode t = n[arg].getType(true);
    return t.isRegExp();
  }
  constexpr static const char* typeName = "regexp";
};

/** Argument is a string */
struct AString
{
  static bool checkArg(TNode n, size_t arg)
  {
    TypeNode t = n[arg].getType(true);
    return t.isString();
  }
  constexpr static const char* typeName = "string";
};

/** 
 * The SimpleTypeRule template can be used to obtain a simple type rule by
 * defining a return type and the argument types (up to three arguments are
 * supported).
 * */
template <class R, class A0 = ANone, class A1 = ANone, class A2 = ANone>
class SimpleTypeRule
{
 public:
  static TypeNode computeType(NodeManager* nm, TNode n, bool check)
  {
    if (check)
    {
      if (!A0::checkArg(n, 0))
      {
        std::stringstream msg;
        msg << "Expecting a " << A0::typeName
            << " term as the first argument in '" << n.getKind() << "'";
        throw TypeCheckingExceptionPrivate(n, msg.str());
      }
      if (!A1::checkArg(n, 1))
      {
        std::stringstream msg;
        msg << "Expecting a " << A1::typeName
            << " term as the second argument in '" << n.getKind() << "'";
        throw TypeCheckingExceptionPrivate(n, msg.str());
      }
      if (!A2::checkArg(n, 2))
      {
        std::stringstream msg;
        msg << "Expecting a " << A2::typeName
            << " term as the third argument in '" << n.getKind() << "'";
        throw TypeCheckingExceptionPrivate(n, msg.str());
      }
    }
    return R::mkType(nm);
  }
};

/** 
 * The SimpleTypeRuleVar template can be used to obtain a simple type rule for
 * operators with a variable number of arguments. It takes the return type and
 * the type of the arguments as template parameters.
 * */
template <class R, class A>
class SimpleTypeRuleVar
{
 public:
  static TypeNode computeType(NodeManager* nm, TNode n, bool check)
  {
    if (check)
    {
      for (size_t i = 0, size = n.getNumChildren(); i < size; i++)
      {
        if (!A::checkArg(n, i))
        {
          std::stringstream msg;
          msg << "Expecting a " << A::typeName << " term as argument " << i
              << " in '" << n.getKind() << "'";
          throw TypeCheckingExceptionPrivate(n, msg.str());
        }
      }
    }
    return R::mkType(nm);
  }
};

}  // namespace expr
}  // namespace CVC4
