/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2025 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Plugin
 */

#include "expr/plugin.h"

namespace cvc5::internal {

Plugin::Plugin(NodeManager* nm) : d_nm(nm) {}

Plugin::~Plugin() {}

}  // namespace cvc5::internal
