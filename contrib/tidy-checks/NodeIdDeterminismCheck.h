/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * A clang-tidy check that identifies potential non-deterministic NodeId assignments
 * in the cvc5 codebase and suggests fixes to enforce deterministic evaluation order.
 */

#pragma once
#include "clang-tidy/ClangTidyCheck.h"
#include "clang/AST/Mangle.h"
#include "llvm/ADT/DenseMap.h"
#include "llvm/ADT/SmallPtrSet.h"

#include <memory>
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
 * The check has two modes of operation.
 *
 * 1. List mode. The set of "NodeId-dependent" functions is provided externally
 *    as a list of fully qualified function names (CSV) via the
 *    'NodeIdDependencyListPath' option, and the check reports every unsequenced
 *    site that contains two or more calls to functions on that list.
 *
 * 2. Dump mode, enabled by the 'DumpDir' option. The check does not report
 *    anything. Instead, for every translation unit it writes a tab-separated
 *    file into 'DumpDir' containing (a) the call-graph edges of all functions
 *    defined in the project, and (b) every unsequenced site in which at least
 *    two operands call project functions, together with the functions each
 *    operand calls. The script 'node_id_determinism_report.py' then computes
 *    the set of NodeId-dependent functions as the transitive closure of the
 *    callers of the minting points, and reports the offending sites. This
 *    makes the whole analysis a single clang-tidy pass over the code base, with
 *    no external call-graph database required. Functions are identified by
 *    their mangled names, so overloads and template instantiations are kept
 *    apart. The 'SourceRoot' option defines the project as the files below
 *    that directory (which should include the build directory, so that
 *    header-only dependencies instantiated with cvc5 types are covered); by
 *    default every non-system header counts as part of the project.
 *
 * 3. Id list mode. Like list mode, but 'NodeIdDependencyIdListPath' names a
 *    file with one function id (as used in dump mode) per line, as written by
 *    the report script's --write-dependency-ids option. Matching by id rather
 *    than by name distinguishes overloads, so the check reports exactly the
 *    sites the report script flags. This lets the report script select the
 *    files with findings, which clang-tidy then re-checks to print its usual
 *    diagnostics and fix-its, honoring NOLINT comments.
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

    /**
     * @brief In dump mode, writes the collected call graph and sites to a file.
     */
    void onEndOfTranslationUnit() override;

    void storeOptions(ClangTidyOptions::OptionMap &Opts) override;

private:
    bool hasMultipleNodeIdDependencies(llvm::ArrayRef<const Expr *> Exprs);

    /**
     * @brief Loads function names from the configured CSV path into NodeIdDependentFunctions.
     */
    void loadNodeIdDependencyList();

    /**
     * @brief Loads function ids (as written by the report script) from the
     * configured path into NodeIdDependentIds.
     */
    void loadNodeIdDependencyIdList();

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

    /**
     * @brief Dispatches an unsequenced site to list mode or dump mode.
     * @param Kind A tag for the kind of site ("call", "ctor", "binop").
     */
    void analyzeSite(StringRef Kind, llvm::ArrayRef<const Expr*> Exprs, SourceLocation Loc);

    // ---- Dump mode ----

    /** @brief Returns a stable identifier (mangled name) for a function. */
    std::string idOf(const FunctionDecl *FD);

    /** @brief Whether the function is declared in the analyzed project. */
    bool isInProject(const FunctionDecl *FD);

    /** @brief Collects project functions called (CallExpr only) anywhere below S. */
    void collectCalledFunctions(const Stmt *S, llvm::SmallPtrSetImpl<const FunctionDecl*> &Out);

    /** @brief Records the direct callees of a function definition. */
    void dumpCallGraph(const FunctionDecl *FD);

    /** @brief Records an unsequenced site if two or more operands call project functions. */
    void dumpSite(StringRef Kind, llvm::ArrayRef<const Expr*> Exprs, SourceLocation Loc);

    std::string NodeIdDependencyListPath;
    std::set<std::string> NodeIdDependentFunctions;
    std::string NodeIdDependencyIdListPath;
    std::set<std::string> NodeIdDependentIds;

    std::string DumpDir;
    std::string SourceRoot;
    bool DumpMode;
    bool IdMode;
    const SourceManager *SM = nullptr;
    std::unique_ptr<MangleContext> Mangler;
    llvm::DenseMap<const FunctionDecl*, std::string> IdCache;
    std::set<std::string> DumpLines;
};

} // namespace clang::tidy::cvc5
