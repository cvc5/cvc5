/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * A clang-tidy check that identifies potential non-deterministic NodeId assignments in 
 * in the cvc5 codebase and suggests fixes to enforce deterministic evaluation order.
 */

#pragma once
#include "clang-tidy/ClangTidyCheck.h"

#include <set>
#include <string>

/**
 * @file NodeIdDeterminismCheck.h
 * @brief Detects non-deterministic NodeId assignments in unsequenced contexts.
 *
 * @section Purpose
 * In cvc5, certain functions modify or rely on a global counter to assign unique 
 * IDs to Nodes. In C++, the evaluation order of function arguments and many 
 * binary operators is unspecified. This check identifies expressions where 
 * multiple ID-dependent calls occur in a context where the compiler is free 
 * to reorder them, leading to non-deterministic solver behavior across 
 * different compilers or optimization levels.
 *
 * @section Sequencing C++17 Sequencing Rules Applied
 * This check specifically accounts for the P0145R3 refinement in C++17:
 * - **Unsequenced:** Function arguments `f(a, b)`, and most binary operators 
 * `a + b`, `a * b`. These are flagged if multiple dependent calls exist.
 * - **Sequenced:** Assignment `a = b`, shift `a << b`, and comma `a, b`. 
 * For these, the LHS and RHS are validated as independent, safe sequences.
 *
 * @section Usage
 * The check requires an external dependency list (CSV) provided via the 
 * 'NodeIdDependencyListPath' option, listing fully qualified function names 
 * that are considered "NodeId-dependent."
 */

namespace clang::tidy::cvc5 {

/**
 * @class NodeIdDeterminismCheck
 * @brief A Clang-Tidy check for enforcing determinism in NodeId generation.
 */
class NodeIdDeterminismCheck : public ClangTidyCheck {
public:
    /**
     * @brief Initializes the check and loads the dependency list.
     * @param Name The name of the check.
     * @param Context The Clang-Tidy context.
     */
    NodeIdDeterminismCheck(StringRef Name, ClangTidyContext *Context);

    /**
     * @brief Registers AST matchers for CallExpr, CXXConstructExpr, and BinaryOperators.
     */
    void registerMatchers(ast_matchers::MatchFinder *Finder) override;

    /**
     * @brief Analyzes matched nodes and applies C++17 sequencing logic to verify safety.
     */
    void check(const ast_matchers::MatchFinder::MatchResult &Result) override;

private:
    bool hasMultipleNodeIdDependencies(llvm::ArrayRef<const Expr *> Exprs);

    /**
     * @brief Loads function names from the configured CSV path into NodeIdDependentFunctions.
     */
    void loadNodeIdDependencyList();

    /**
     * @brief Recursively searches an expression for a call to a NodeId-dependent function.
     * @param S The statement/expression to search.
     * @return Pointer to the found CallExpr, or nullptr if none found.
     */
    const CallExpr* findNestedNodeIdDependentCall(const Stmt *S);

    /**
     * @brief Identifies if an array of expressions contains more than one dependent call.
     * @param Exprs The list of expressions (e.g., function arguments) to validate.
     * @param Loc The source location for reporting potential warnings.
     */
    void verifyNodeIdAssignmentSequencing(llvm::ArrayRef<const Expr*> Exprs, SourceLocation Loc);

    std::string NodeIdDependencyListPath;
    std::set<std::string> NodeIdDependentFunctions;
};

} // namespace clang::tidy::cvc5
