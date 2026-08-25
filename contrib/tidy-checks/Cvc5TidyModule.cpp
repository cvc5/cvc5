/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Implementation of the cvc5 clang-tidy module, which registers custom checks for
 * the cvc5 codebase.
 */

#include "clang-tidy/ClangTidy.h"
#include "clang-tidy/ClangTidyModule.h"
#include "clang-tidy/ClangTidyModuleRegistry.h"
#include "NodeIdDeterminismCheck.h"

using namespace clang::tidy;

namespace {

class Cvc5TidyModule : public ClangTidyModule {
public:
  void addCheckFactories(ClangTidyCheckFactories &Factories) override {
    Factories.registerCheck<cvc5::NodeIdDeterminismCheck>(
        "cvc5-node-id-determinism");
  }
};

static ClangTidyModuleRegistry::Add<Cvc5TidyModule>
    X("cvc5-module", "cvc5 clang-tidy checks");

} // namespace

