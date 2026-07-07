/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 */

#include "NodeIdDeterminismCheck.h"

#include "clang/AST/ASTContext.h"
#include "clang/ASTMatchers/ASTMatchFinder.h"
#include "clang/Lex/Lexer.h"

#include <fstream>

using namespace clang::ast_matchers;

namespace clang::tidy::cvc5 {

NodeIdDeterminismCheck::NodeIdDeterminismCheck(StringRef Name, ClangTidyContext *Context)
    : ClangTidyCheck(Name, Context),
      NodeIdDependencyListPath(Options.get("NodeIdDependencyListPath", "")) {
  if (NodeIdDependencyListPath.empty()) {
    llvm::errs() << "Warning: NodeIdDependencyListPath not set.\n";
  } else {
    loadNodeIdDependencyList();
  }
}

void NodeIdDeterminismCheck::loadNodeIdDependencyList() {
  std::ifstream File(NodeIdDependencyListPath);
  if (!File.is_open()) {
    llvm::errs() << "Error: Could not open NodeId dependency list at "
                 << NodeIdDependencyListPath << "\n";
    return;
  }

  std::string Line;
  while (std::getline(File, Line)) {
    // Discard column name and strip CSV quotes
    if (Line == "col0" || Line.empty()) continue;
    if (Line.size() >= 2 && Line.front() == '"' && Line.back() == '"') {
      Line = Line.substr(1, Line.size() - 2);
    }
    // C++17 sequences operator<< and operator>>, so these are safe.
    if (Line.find("operator<<") == std::string::npos && 
        Line.find("operator>>") == std::string::npos) {
      NodeIdDependentFunctions.insert(Line);
    }
  }
}

void NodeIdDeterminismCheck::registerMatchers(MatchFinder *Finder) {
  // Match function calls, member calls, and overloaded operators
  Finder->addMatcher(callExpr().bind("call_site"), this);

  // Match constructor calls (e.g., Node n(id(), id()))
  Finder->addMatcher(cxxConstructExpr().bind("call_site"), this);

  // Match built-in binary operators, excluding those with strict C++17 sequencing
  Finder->addMatcher(
      binaryOperator(unless(anyOf(
          hasOperatorName("&&"), hasOperatorName("||"),
          hasOperatorName(","), hasOperatorName("<<"), hasOperatorName(">>"))))
          .bind("bin_op"),
      this);
}

bool NodeIdDeterminismCheck::hasMultipleNodeIdDependencies(llvm::ArrayRef<const Expr *> Exprs) {
  size_t count = 0;
  for (const Expr *E : Exprs) {
    if (findNestedNodeIdDependentCall(E)) {
      count++;
    }
    if (count > 1) return true;
  }
  return false;
}

void NodeIdDeterminismCheck::check(const MatchFinder::MatchResult &Result) {
  // 1. Specialized Case: NodeManager::mkNode
  // Detect nm->mkNode(k, f(), g()) and suggest nm->mkNode(k, {f(), g()}).
  //
  // The matcher fires once per call-expr node in the AST, so for nested calls
  // like nm->mkNode(k, nm->mkNode(k, f(), g()), w()) it fires on both the
  // inner and the outer mkNode independently. We therefore never skip or
  // early-return here, every mkNode site is evaluated on its own merits and
  // gets its own fix-it if needed.
  if (const auto *CE = Result.Nodes.getNodeAs<CallExpr>("call_site")) {
    if (const auto *FD = CE->getDirectCallee()) {
      if (FD->getDeclName().isIdentifier() && FD->getName() == "mkNode"
          && CE->getNumArgs() > 2) {
        // Arg index 0 is the Kind; indices 1..N are the child Node arguments.
        unsigned NumArgs = CE->getNumArgs();
        llvm::SmallVector<const Expr *, 4> NodeArgs;
        for (unsigned i = 1; i < NumArgs; ++i)
          NodeArgs.push_back(CE->getArg(i));

        // Only flag when at least two child args contain NodeId-dependent
        // calls, since a single such call cannot race with itself.
        if (hasMultipleNodeIdDependencies(NodeArgs)) {
          const ASTContext *Ctx = Result.Context;
          const SourceManager &SM = Ctx->getSourceManager();
          const LangOptions &LO = Ctx->getLangOpts();

          SourceLocation ArgsBegin = NodeArgs.front()->getBeginLoc();
          SourceLocation ArgsEnd = Lexer::getLocForEndOfToken(
              NodeArgs.back()->getEndLoc(), 0, SM, LO);

          // Re-lex each argument's source text and wrap them in braces.
          // Braced-list initialization in C++17 is sequenced left-to-right,
          // which eliminates the evaluation-order non-determinism.
          std::string BracedArgs = "{";
          for (unsigned i = 0; i < NodeArgs.size(); ++i) {
            if (i > 0) BracedArgs += ", ";
            CharSourceRange ArgRange = CharSourceRange::getTokenRange(
                NodeArgs[i]->getBeginLoc(), NodeArgs[i]->getEndLoc());
            BracedArgs += Lexer::getSourceText(ArgRange, SM, LO).str();
          }
          BracedArgs += "}";

          auto Diag = diag(
              CE->getBeginLoc(),
              "potential non-deterministic NodeId assignment in mkNode(); "
              "wrap node arguments in braces to enforce left-to-right "
              "sequencing");
          Diag << FixItHint::CreateReplacement(
              CharSourceRange::getCharRange(ArgsBegin, ArgsEnd), BracedArgs);
        }

        // Always skip the general handler for mkNode calls — it would
        // double-report the same site without offering a fix.
        return;
      }
    }
  }

  // 2. Handle General Function/Constructor/Operator Calls
  if (const auto *CE = Result.Nodes.getNodeAs<CallExpr>("call_site")) {
    // Note: CXXMemberCallExpr and CXXOperatorCallExpr are subclasses of CallExpr
    // For Assignment/Shift overloads, C++17 defines sequencing.
    if (const auto *OCE = dyn_cast<CXXOperatorCallExpr>(CE)) {
       OverloadedOperatorKind OO = OCE->getOperator();
       if (OO >= OO_Equal && OO <= OO_PipeEqual) { // Assignment family
           // C++17: RHS is sequenced before LHS. Check them as separate timelines.
           verifyNodeIdAssignmentSequencing({OCE->getArg(1)}, OCE->getBeginLoc()); // RHS
           verifyNodeIdAssignmentSequencing({OCE->getArg(0)}, OCE->getBeginLoc()); // LHS
           return;
       }
       // C++17 sequences overloaded operator<< and operator>> left-to-right
       // (each call is sequenced before the next), so stream expressions like
       // a << f() << g() are safe regardless of NodeId-dependent calls.
       if (OO == OO_LessLess || OO == OO_GreaterGreater) return;
    }
    
    llvm::SmallVector<const Expr *, 8> Args(CE->arguments());
    verifyNodeIdAssignmentSequencing(Args, CE->getBeginLoc());
  }

  // Handle Constructor Calls
  if (const auto *Ctor = Result.Nodes.getNodeAs<CXXConstructExpr>("call_site")) {
    // Note: If this is a list-initialization (braced), it's sequenced and safe in C++17.
    if (!Ctor->isListInitialization()) {
      llvm::SmallVector<const Expr *, 8> Args(Ctor->arguments());
      verifyNodeIdAssignmentSequencing(Args, Ctor->getBeginLoc());
    }
  }

  // Handle Built-in Binary Operators
  if (const auto *BO = Result.Nodes.getNodeAs<BinaryOperator>("bin_op")) {
    if (BO->isAssignmentOp()) {
      // RHS is sequenced BEFORE LHS in C++17. Check them independently.
      verifyNodeIdAssignmentSequencing({BO->getLHS()}, BO->getOperatorLoc());
      verifyNodeIdAssignmentSequencing({BO->getRHS()}, BO->getOperatorLoc());
    } else {
      // Unsequenced (e.g., a + b). Both sides together must not have >1 call.
      verifyNodeIdAssignmentSequencing({BO->getLHS(), BO->getRHS()}, BO->getOperatorLoc());
    }
  }
}

const CallExpr* NodeIdDeterminismCheck::findNestedNodeIdDependentCall(const Stmt *S) {
  if (!S) return nullptr;

  if (const auto *CE = dyn_cast<CallExpr>(S)) {
    if (const auto *FD = CE->getDirectCallee()) {
      if (NodeIdDependentFunctions.count(FD->getQualifiedNameAsString())) 
        return CE;
    }
  }

  // Recurse into sub-expressions
  for (const Stmt *Child : S->children()) {
    if (const auto *Found = findNestedNodeIdDependentCall(Child)) return Found;
  }
  return nullptr;
}

void NodeIdDeterminismCheck::verifyNodeIdAssignmentSequencing(
    llvm::ArrayRef<const Expr*> Exprs, SourceLocation Loc) {
  std::set<const CallExpr*> FoundCalls;
  for (const Expr *E : Exprs) {
    if (const auto *C = findNestedNodeIdDependentCall(E)) {
      FoundCalls.insert(C);
    }
  }

  if (FoundCalls.size() > 1) {
    auto D = diag(Loc, "potential non-deterministic NodeId assignment");
    for (const auto *C : FoundCalls) {
      D << C->getSourceRange();
    }
  }
}

} // namespace clang::tidy::cvc5
