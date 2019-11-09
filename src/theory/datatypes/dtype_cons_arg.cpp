/*********************                                                        */
/*! \file dtype.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief A class representing a datatype definition
 **/

#include "theory/datatypes/dtype_cons_arg.h"

#include "options/set_language.h"

using namespace CVC4::kind;

namespace CVC4 {

DTypeConstructorArg::DTypeConstructorArg(std::string name, Node selector)
    : d_name(name), d_selector(selector), d_resolved(false)
{
  Trace("ajr-temp") << "DTypeConstructorArg::DTypeConstructorArg" << std::endl;
  PrettyCheckArgument(
      name != "",
      name,
      "cannot construct a datatype constructor arg without a name");
}

std::string DTypeConstructorArg::getName() const
{
  return d_name;
}

Node DTypeConstructorArg::getSelector() const
{
  PrettyCheckArgument(
      isResolved(),
      this,
      "cannot get a selector for an unresolved datatype constructor");
  return d_selector;
}

Node DTypeConstructorArg::getConstructor() const
{
  PrettyCheckArgument(isResolved(),
                      this,
                      "cannot get a associated constructor for argument of an "
                      "unresolved datatype constructor");
  return d_constructor;
}

TypeNode DTypeConstructorArg::getType() const
{
  return getSelector().getType();
}

TypeNode DTypeConstructorArg::getRangeType() const
{
  return getType().getRangeType();
}

bool DTypeConstructorArg::isResolved() const
{
  // We could just write:
  //
  //   return !d_selector.isNull() && d_selector.getType().isSelector();
  //
  // HOWEVER, this causes problems in NodeManager tear-down, because
  // the attributes are removed before the pool is purged.  When the
  // pool is purged, this triggers an equality test between DTypes,
  // and this triggers a call to isResolved(), which breaks because
  // d_selector has no type after attributes are stripped.
  //
  // This problem, coupled with the fact that this function is called
  // _often_, means we should just use a boolean flag.
  //
  return d_resolved;
}

void DTypeConstructorArg::toStream(std::ostream& out) const
{
  Trace("ajr-temp") << "DTypeConstructorArg::toStream" << std::endl;
  out << getName() << ": ";

  TypeNode t;
  if (isResolved())
  {
    t = getRangeType();
  }
  else if (d_selector.isNull())
  {
    std::string typeName = d_name.substr(d_name.find('\0') + 1);
    out << ((typeName == "") ? "[self]" : typeName);
    return;
  }
  else
  {
    t = d_selector.getType();
  }
  out << t;
}

std::ostream& operator<<(std::ostream& os, const DTypeConstructorArg& arg)
{
  // can only output datatypes in the CVC4 native language
  language::SetLanguage::Scope ls(os, language::output::LANG_CVC4);
  arg.toStream(os);
  return os;
}

}  // namespace CVC4
