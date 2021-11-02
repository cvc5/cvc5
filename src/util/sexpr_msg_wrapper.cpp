/******************************************************************************
 * Top contributors (to current version):
 *   Gereon Kremer
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * A simple wrapper to be used in Env::outputMsg(tag) and
 * EnvObj::outputMsg(tag).
 */

#include "util/sexpr_msg_wrapper.h"

#include <iostream>

#include "options/base_options.h"

namespace cvc5 {

SExprMsgWrapper::SExprMsgWrapper(std::ostream& os, OutputTag tag)
    : d_os(os), d_tag(tag)
{
  d_os << "(message \"";
}
SExprMsgWrapper::~SExprMsgWrapper()
{
  d_os << "\" :" << d_tag << ")" << std::endl;
}

}  // namespace cvc5
