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
#include "clang/AST/GlobalDecl.h"
#include "clang/ASTMatchers/ASTMatchFinder.h"
#include "clang/Lex/Lexer.h"
#include "llvm/ADT/StringExtras.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Support/xxhash.h"

#include <fstream>

using namespace clang::ast_matchers;

namespace clang::tidy::cvc5 {

NodeIdDeterminismCheck::NodeIdDeterminismCheck(StringRef Name, ClangTidyContext *Context)
    : ClangTidyCheck(Name, Context),
      NodeIdDependencyListPath(Options.get("NodeIdDependencyListPath", "")),
      NodeIdDependencyIdListPath(Options.get("NodeIdDependencyIdListPath", "")),
      DumpDir(Options.get("DumpDir", "")),
      SourceRoot(Options.get("SourceRoot", "")),
      DumpMode(!DumpDir.empty()),
      IdMode(!DumpMode && !NodeIdDependencyIdListPath.empty()) {
  if (DumpMode) return;
  if (IdMode) {
    loadNodeIdDependencyIdList();
  } else if (NodeIdDependencyListPath.empty()) {
    llvm::errs() << "Warning: NodeIdDependencyListPath not set.\n";
  } else {
    loadNodeIdDependencyList();
  }
}

void NodeIdDeterminismCheck::storeOptions(ClangTidyOptions::OptionMap &Opts) {
  Options.store(Opts, "NodeIdDependencyListPath", NodeIdDependencyListPath);
  Options.store(Opts, "NodeIdDependencyIdListPath", NodeIdDependencyIdListPath);
  Options.store(Opts, "DumpDir", DumpDir);
  Options.store(Opts, "SourceRoot", SourceRoot);
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

void NodeIdDeterminismCheck::loadNodeIdDependencyIdList() {
  std::ifstream File(NodeIdDependencyIdListPath);
  if (!File.is_open()) {
    llvm::errs() << "Error: Could not open NodeId dependency id list at "
                 << NodeIdDependencyIdListPath << "\n";
    return;
  }
  std::string Line;
  while (std::getline(File, Line)) {
    if (!Line.empty()) NodeIdDependentIds.insert(Line);
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

  // In dump mode, additionally record the call graph of every function
  // definition, which the report script needs to compute the dependent set.
  if (DumpMode) {
    Finder->addMatcher(functionDecl(isDefinition(), hasBody(stmt())).bind("fn"),
                       this);
  }
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
  if (DumpMode || IdMode) {
    SM = Result.SourceManager;
    if (!Mangler) Mangler.reset(Result.Context->createMangleContext());
  }

  if (const auto *FD = Result.Nodes.getNodeAs<FunctionDecl>("fn")) {
    dumpCallGraph(FD);
    return;
  }

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

        if (DumpMode) {
          dumpSite("mkNode", NodeArgs, CE->getBeginLoc());
          return;
        }

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
           analyzeSite("call", {OCE->getArg(1)}, OCE->getBeginLoc()); // RHS
           analyzeSite("call", {OCE->getArg(0)}, OCE->getBeginLoc()); // LHS
           return;
       }
       // C++17 sequences overloaded operator<< and operator>> left-to-right
       // (each call is sequenced before the next), so stream expressions like
       // a << f() << g() are safe regardless of NodeId-dependent calls.
       if (OO == OO_LessLess || OO == OO_GreaterGreater) return;
    }
    
    llvm::SmallVector<const Expr *, 8> Args(CE->arguments());
    analyzeSite("call", Args, CE->getBeginLoc());
  }

  // Handle Constructor Calls
  if (const auto *Ctor = Result.Nodes.getNodeAs<CXXConstructExpr>("call_site")) {
    // Note: If this is a list-initialization (braced), it's sequenced and safe in C++17.
    if (!Ctor->isListInitialization()) {
      llvm::SmallVector<const Expr *, 8> Args(Ctor->arguments());
      analyzeSite("ctor", Args, Ctor->getBeginLoc());
    }
  }

  // Handle Built-in Binary Operators
  if (const auto *BO = Result.Nodes.getNodeAs<BinaryOperator>("bin_op")) {
    if (BO->isAssignmentOp()) {
      // RHS is sequenced BEFORE LHS in C++17. Check them independently.
      analyzeSite("binop", {BO->getLHS()}, BO->getOperatorLoc());
      analyzeSite("binop", {BO->getRHS()}, BO->getOperatorLoc());
    } else {
      // Unsequenced (e.g., a + b). Both sides together must not have >1 call.
      analyzeSite("binop", {BO->getLHS(), BO->getRHS()}, BO->getOperatorLoc());
    }
  }
}

void NodeIdDeterminismCheck::analyzeSite(StringRef Kind,
                                         llvm::ArrayRef<const Expr *> Exprs,
                                         SourceLocation Loc) {
  // A single operand can never contain two unsequenced calls relative to
  // itself, so there is nothing to analyze (in either mode).
  if (Exprs.size() < 2) return;
  if (DumpMode) {
    dumpSite(Kind, Exprs, Loc);
  } else {
    verifyNodeIdAssignmentSequencing(Exprs, Loc);
  }
}

const CallExpr* NodeIdDeterminismCheck::findNestedNodeIdDependentCall(const Stmt *S) {
  if (!S) return nullptr;

  if (const auto *CE = dyn_cast<CallExpr>(S)) {
    if (const auto *FD = CE->getDirectCallee()) {
      if (IdMode ? NodeIdDependentIds.count(idOf(FD)) > 0
                 : NodeIdDependentFunctions.count(FD->getQualifiedNameAsString()) > 0)
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

// ---------------------------------------------------------------------------
// Dump mode
// ---------------------------------------------------------------------------

bool NodeIdDeterminismCheck::isInProject(const FunctionDecl *FD) {
  SourceLocation Loc = SM->getExpansionLoc(FD->getLocation());
  if (Loc.isInvalid()) return false;
  if (SourceRoot.empty()) return !SM->isInSystemHeader(Loc);
  return SM->getFilename(Loc).starts_with(SourceRoot);
}

std::string NodeIdDeterminismCheck::idOf(const FunctionDecl *FD) {
  FD = FD->getCanonicalDecl();
  auto It = IdCache.find(FD);
  if (It != IdCache.end()) return It->second;

  std::string Id;
  // Mangled names distinguish overloads and template instantiations and are
  // stable across translation units. Templated entities (patterns) cannot be
  // mangled; they are only reached from other patterns, which we skip anyway.
  if (Mangler && !FD->isTemplated() && !FD->isDependentContext()
      && Mangler->shouldMangleDeclName(FD)) {
    llvm::raw_string_ostream OS(Id);
    if (const auto *Ctor = dyn_cast<CXXConstructorDecl>(FD))
      Mangler->mangleName(GlobalDecl(Ctor, Ctor_Complete), OS);
    else if (const auto *Dtor = dyn_cast<CXXDestructorDecl>(FD))
      Mangler->mangleName(GlobalDecl(Dtor, Dtor_Complete), OS);
    else
      Mangler->mangleName(GlobalDecl(FD), OS);
  }
  if (Id.empty()) Id = FD->getQualifiedNameAsString();

  if (DumpMode)
    DumpLines.insert("N\t" + Id + "\t" + FD->getQualifiedNameAsString());
  IdCache[FD] = Id;
  return Id;
}

void NodeIdDeterminismCheck::collectCalledFunctions(
    const Stmt *S, llvm::SmallPtrSetImpl<const FunctionDecl *> &Out) {
  if (!S) return;
  // Same shape as findNestedNodeIdDependentCall(): only CallExpr nodes count,
  // and the whole operand subtree is searched.
  if (const auto *CE = dyn_cast<CallExpr>(S)) {
    if (const FunctionDecl *FD = CE->getDirectCallee()) {
      if (isInProject(FD)) Out.insert(FD);
    }
  }
  for (const Stmt *Child : S->children()) collectCalledFunctions(Child, Out);
}

namespace {
// Collects every function invoked below S, including constructors.
void collectAllCallees(const Stmt *S,
                       llvm::SmallPtrSetImpl<const FunctionDecl *> &Out) {
  if (!S) return;
  if (const auto *CE = dyn_cast<CallExpr>(S)) {
    if (const FunctionDecl *FD = CE->getDirectCallee()) Out.insert(FD);
  } else if (const auto *CC = dyn_cast<CXXConstructExpr>(S)) {
    Out.insert(CC->getConstructor());
  }
  for (const Stmt *Child : S->children()) collectAllCallees(Child, Out);
}
} // namespace

void NodeIdDeterminismCheck::dumpCallGraph(const FunctionDecl *FD) {
  // Uninstantiated templates have unresolved callees; their instantiations
  // are visited separately.
  if (FD->isDependentContext() || FD->isTemplated()) return;
  if (!isInProject(FD)) return;

  llvm::SmallPtrSet<const FunctionDecl *, 32> Callees;
  collectAllCallees(FD->getBody(), Callees);
  if (const auto *Ctor = dyn_cast<CXXConstructorDecl>(FD)) {
    for (const CXXCtorInitializer *Init : Ctor->inits())
      collectAllCallees(Init->getInit(), Callees);
  }
  if (Callees.empty()) return;

  std::string Caller = idOf(FD);
  for (const FunctionDecl *Callee : Callees) {
    // Only project functions can become NodeId-dependent.
    if (!isInProject(Callee)) continue;
    DumpLines.insert("E\t" + Caller + "\t" + idOf(Callee));
  }
}

void NodeIdDeterminismCheck::dumpSite(StringRef Kind,
                                      llvm::ArrayRef<const Expr *> Exprs,
                                      SourceLocation Loc) {
  llvm::SmallVector<llvm::SmallPtrSet<const FunctionDecl *, 4>, 4> PerOperand(
      Exprs.size());
  unsigned NonEmpty = 0;
  for (size_t i = 0; i < Exprs.size(); ++i) {
    collectCalledFunctions(Exprs[i], PerOperand[i]);
    if (!PerOperand[i].empty()) ++NonEmpty;
  }
  // Only sites with at least two call-containing operands can ever be flagged.
  if (NonEmpty < 2) return;

  PresumedLoc P = SM->getPresumedLoc(SM->getExpansionLoc(Loc));
  if (P.isInvalid()) return;
  std::string Where = std::string(P.getFilename()) + ":"
                      + std::to_string(P.getLine()) + ":"
                      + std::to_string(P.getColumn());
  // Different sites can share the begin location (e.g. an overloaded operator
  // call and the call that is its first operand), so the end of the last
  // operand is recorded as well to keep them apart.
  PresumedLoc E = SM->getPresumedLoc(SM->getExpansionLoc(Exprs.back()->getEndLoc()));
  std::string End = E.isValid() ? std::to_string(E.getLine()) + ":"
                                      + std::to_string(E.getColumn())
                                : "?";

  for (size_t i = 0; i < Exprs.size(); ++i) {
    for (const FunctionDecl *FD : PerOperand[i]) {
      DumpLines.insert("S\t" + Where + "\t" + Kind.str() + "\t" + End + "\t"
                       + std::to_string(i) + "\t" + idOf(FD));
    }
  }
}

void NodeIdDeterminismCheck::onEndOfTranslationUnit() {
  if (!DumpMode) {
    // The mangle context and the cached ids do not outlive the translation
    // unit.
    IdCache.clear();
    Mangler.reset();
    SM = nullptr;
    return;
  }
  if (!DumpLines.empty() && SM) {
    std::string MainFile;
    if (auto FE = SM->getFileEntryRefForID(SM->getMainFileID()))
      MainFile = FE->getName().str();
    std::string Path = DumpDir + "/" + llvm::utohexstr(llvm::xxh3_64bits(MainFile))
                       + ".tsv";
    std::ofstream Out(Path);
    if (!Out.is_open()) {
      llvm::errs() << "Error: Could not write NodeId dump to " << Path << "\n";
    } else {
      Out << "T\t" << MainFile << "\n";
      for (const std::string &Line : DumpLines) Out << Line << "\n";
    }
  }
  // AST nodes and the mangle context do not outlive the translation unit.
  DumpLines.clear();
  IdCache.clear();
  Mangler.reset();
  SM = nullptr;
}

} // namespace clang::tidy::cvc5
