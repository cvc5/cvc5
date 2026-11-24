/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * The cvc5 java API.
 */

package io.github.cvc5;

import io.github.cvc5.TermManager;
import io.github.cvc5.modes.BlockModelsMode;
import io.github.cvc5.modes.FindSynthTarget;
import io.github.cvc5.modes.LearnedLitType;
import io.github.cvc5.modes.ProofComponent;
import io.github.cvc5.modes.ProofFormat;
import java.io.IOException;
import java.lang.ref.Reference;
import java.util.*;

/**
 * A cvc5 solver.
 */
public class Solver extends AbstractPointer implements AutoCloseable
{
  /**
   * The term manager of this solver: a wrapper of the solver's own copy of
   * the term manager it was created with, created on first use. It remains
   * valid after the term manager passed to the constructor has been released.
   */
  private TermManager d_tm;

  static
  {
    Utils.loadLibraries();
  }

  /**
   * Objects that native code calls back into (plugins and oracle bridges).
   * Native code references them only weakly, so they are kept alive here for
   * the lifetime of this solver. A strong native reference would keep this
   * solver's term manager reachable (plugins reference it) and thus prevent
   * the solver from ever being reclaimed automatically.
   */
  private final List<Object> callbacks = new ArrayList<>();

  /**
   * The wrapper of the connected terminator, if any. Like the callbacks above,
   * native code references it only weakly.
   */
  private TerminatorWrapper terminatorWrapper;

  /**
   * Create solver instance.
   * @param tm The associated term manager.
   */
  public Solver(TermManager tm)
  {
    super(tm.ctx, Solver.newSolver(tm.getPointer()), Solver::deletePointer);
  }
  private static native long newSolver(long tmPointer);

  private static native void deletePointer(long pointer);

  /**
   * Free the native solver, see {@code deletePointer()}.
   */
  @Override
  public void close()
  {
    deletePointer();
  }

  protected String toString(long pointer)
  {
    throw new UnsupportedOperationException("Solver.toString() is not supported in the cpp api");
  }

  @Override
  public boolean equals(Object s)
  {
    if (this == s)
    {
      return true;
    }
    if (s == null || getClass() != s.getClass())
    {
      return false;
    }
    Solver solver = (Solver) s;
    if (this.pointer == solver.pointer)
    {
      return true;
    }
    return false;
  }

  /**
   * Return a hash code value for this solver.
   *
   * The hash code is derived from the underlying native pointer, which is what
   * {@link #equals(Object)} compares, so that instances that are equal have the
   * same hash code.
   *
   * @return a hash code value for this solver
   */
  @Override
  public int hashCode()
  {
    return Long.hashCode(getPointer());
  }

  /**
   * Get the associated term manager instance.
   *
   * <p>The returned object refers to the same term manager as the one this
   * solver was created with: closing it releases that term manager and every
   * object derived from it, including this solver, see
   * {@link TermManager#close()}.</p>
   * @return The term manager.
   */
  public TermManager getTermManager()
  {
    if (d_tm == null)
    {
      d_tm = new TermManager(ctx, getTermManager(getPointer()));
    }
    return d_tm;
  }
  private native long getTermManager(long pointer);

  /* .................................................................... */
  /* Formula Handling                                                     */
  /* .................................................................... */

  /**
   * Simplify a term or formula based on rewriting.
   *
   * @api.note This function is experimental and may change in future versions.
   *
   * @param t The term to simplify.
   * @return The simplified term.
   */
  public Term simplify(Term t)
  {
    try
    {
      long termPointer = simplify(getPointer(), t.getPointer());
      return new Term(ctx, termPointer);
    }
    finally
    {
      checkTerminator();
    }
  }

  private native long simplify(long pointer, long termPointer);

  /**
   * Simplify a term or formula based on rewriting and (optionally) applying
   * substitutions for solved variables.
   *
   * If applySubs is true, then for example, if `(= x 0)` was asserted to this
   * solver, this method may replace occurrences of `x` with `0`.
   *
   * @api.note This function is experimental and may change in future versions.
   *
   * @param t The term to simplify.
   * @param applySubs Whether to apply substitutions for solved variables.
   * @return The simplified term.
   */
  public Term simplify(Term t, boolean applySubs)
  {
    try
    {
      long termPointer = simplify(getPointer(), t.getPointer(), applySubs);
      return new Term(ctx, termPointer);
    }
    finally
    {
      checkTerminator();
    }
  }

  private native long simplify(long pointer, long termPointer, boolean applySubs);
  /**
   * Assert a formula.
   * SMT-LIB:
   * {@code
   *   ( assert <term> )
   * }
   * @param term The formula to assert.
   */
  public void assertFormula(Term term)
  {
    assertFormula(getPointer(), term.getPointer());
  }

  private native void assertFormula(long pointer, long termPointer);

  /**
   * Check satisfiability.
   *
   * SMT-LIB:
   * {@code
   *   ( check-sat )
   * }
   *
   * @return The result of the satisfiability check.
   */
  public Result checkSat()
  {
    try
    {
      long resultPointer = checkSat(getPointer());
      return new Result(ctx, resultPointer);
    }
    finally
    {
      checkTerminator();
    }
  }

  private native long checkSat(long pointer);
  /**
   * Check satisfiability assuming the given formula.
   *
   * SMT-LIB:
   * {@code
   *   ( check-sat-assuming ( <prop_literal> ) )
   * }
   *
   * @param assumption The formula to assume.
   * @return The result of the satisfiability check.
   */
  public Result checkSatAssuming(Term assumption)
  {
    try
    {
      long resultPointer = checkSatAssuming(getPointer(), assumption.getPointer());
      // The native call may re-enter Java code (plugins, oracles), which may
      // release native objects whose wrappers are unreachable.
      Reference.reachabilityFence(assumption);
      return new Result(ctx, resultPointer);
    }
    finally
    {
      checkTerminator();
    }
  }

  private native long checkSatAssuming(long pointer, long assumptionPointer);

  /**
   * Check satisfiability assuming the given formulas.
   *
   * SMT-LIB:
   * {@code
   *   ( check-sat-assuming ( <prop_literal>+ ) )
   * }
   *
   * @param assumptions The formulas to assume.
   * @return The result of the satisfiability check.
   */
  public Result checkSatAssuming(Term[] assumptions)
  {
    try
    {
      long[] pointers = Utils.getPointers(assumptions);
      long resultPointer = checkSatAssuming(getPointer(), pointers);
      // The native call may re-enter Java code (plugins, oracles), which may
      // release native objects whose wrappers are unreachable.
      Reference.reachabilityFence(assumptions);
      return new Result(ctx, resultPointer);
    }
    finally
    {
      checkTerminator();
    }
  }

  private native long checkSatAssuming(long pointer, long[] assumptionPointers);

  /**
   * Create datatype sort.
   *
   * SMT-LIB:
   * {@code
   *   ( declare-datatype <symbol> <datatype_decl> )
   * }
   *
   * @param symbol The name of the datatype sort.
   * @param ctors The constructor declarations of the datatype sort.
   * @return The datatype sort.
   */
  public Sort declareDatatype(String symbol, DatatypeConstructorDecl[] ctors)
  {
    long[] pointers = Utils.getPointers(ctors);
    long sortPointer = declareDatatype(getPointer(), symbol, pointers);
    return new Sort(ctx, sortPointer);
  }

  private native long declareDatatype(long pointer, String symbol, long[] declPointers);

  /**
   * Declare n-ary function symbol.
   *
   * SMT-LIB:
   * {@code
   *   ( declare-fun <symbol> ( <sort>* ) <sort> )
   * }
   *
   * @param symbol The name of the function.
   * @param sorts The sorts of the parameters to this function.
   * @param sort The sort of the return value of this function.
   * @return The function.
   */
  public Term declareFun(String symbol, Sort[] sorts, Sort sort)
  {
    long[] sortPointers = Utils.getPointers(sorts);
    long termPointer = declareFun(getPointer(), symbol, sortPointers, sort.getPointer());
    return new Term(ctx, termPointer);
  }

  private native long declareFun(
      long pointer, String symbol, long[] sortPointers, long sortPointer);

  /**
   * Declare n-ary function symbol.
   *
   * SMT-LIB:
   * {@code
   *   ( declare-fun <symbol> ( <sort>* ) <sort> )
   * }
   *
   * @param symbol The name of the function.
   * @param sorts The sorts of the parameters to this function.
   * @param sort The sort of the return value of this function.
   * @param fresh If true, then this method always returns a new Term.
   * Otherwise, this method will always return the same Term
   * for each call with the given sorts and symbol where fresh is false.
   * @return The function.
   */
  public Term declareFun(String symbol, Sort[] sorts, Sort sort, boolean fresh)
  {
    long[] sortPointers = Utils.getPointers(sorts);
    long termPointer = declareFun(getPointer(), symbol, sortPointers, sort.getPointer(), fresh);
    return new Term(ctx, termPointer);
  }

  private native long declareFun(
      long pointer, String symbol, long[] sortPointers, long sortPointer, boolean fresh);
  /**
   * Declare uninterpreted sort.
   *
   * SMT-LIB:
   * {@code
   *   ( declare-sort <symbol> <numeral> )
   * }
   *
   * @api.note This corresponds to {@link TermManager#mkUninterpretedSort} if
   *           arity = 0, and to
   *           {@link TermManager#mkUninterpretedSortConstructorSort} if
   *           arity &gt; 0.
   *
   * @param symbol The name of the sort.
   * @param arity The arity of the sort.
   * @return The sort.
   * @throws CVC5ApiException on error
   */
  public Sort declareSort(String symbol, int arity) throws CVC5ApiException
  {
    Utils.validateUnsigned(arity, "arity");
    long sortPointer = declareSort(getPointer(), symbol, arity);
    return new Sort(ctx, sortPointer);
  }

  private native long declareSort(long pointer, String symbol, int arity);

  /**
   * Declare uninterpreted sort.
   *
   * SMT-LIB:
   * {@code
   *   ( declare-sort <symbol> <numeral> )
   * }
   *
   * @api.note This corresponds to {@link TermManager#mkUninterpretedSort} if
   *           arity = 0, and to
   *           {@link TermManager#mkUninterpretedSortConstructorSort} if
   *           arity &gt; 0.
   *
   * @param symbol The name of the sort.
   * @param arity The arity of the sort.
   * @param fresh If true, then this method always returns a new Sort.
   * Otherwise, this method will always return the same Sort
   * for each call with the given arity and symbol where fresh is false.
   * @return The sort.
   * @throws CVC5ApiException on error
   */
  public Sort declareSort(String symbol, int arity, boolean fresh) throws CVC5ApiException
  {
    Utils.validateUnsigned(arity, "arity");
    long sortPointer = declareSort(getPointer(), symbol, arity, fresh);
    return new Sort(ctx, sortPointer);
  }

  private native long declareSort(long pointer, String symbol, int arity, boolean fresh);

  /**
   * Define n-ary function in the current context.
   *
   * SMT-LIB:
   * {@code
   *   ( define-fun <function_def> )
   * }
   *
   * @param symbol The name of the function.
   * @param boundVars The parameters to this function.
   * @param sort The sort of the return value of this function.
   * @param term The function body.
   * @return The function.
   */
  public Term defineFun(String symbol, Term[] boundVars, Sort sort, Term term)
  {
    return defineFun(symbol, boundVars, sort, term, false);
  }

  /**
   * Define n-ary function.
   *
   * SMT-LIB:
   * {@code
   *   ( define-fun <function_def> )
   * }
   *
   * @param symbol The name of the function.
   * @param boundVars The parameters to this function.
   * @param sort The sort of the return value of this function.
   * @param term The function body.
   * @param global Determines whether this definition is global (i.e., persists
   *               when popping the context).
   * @return The function.
   */
  public Term defineFun(String symbol, Term[] boundVars, Sort sort, Term term, boolean global)
  {
    long[] boundVarPointers = Utils.getPointers(boundVars);
    long termPointer = defineFun(
        getPointer(), symbol, boundVarPointers, sort.getPointer(), term.getPointer(), global);
    return new Term(ctx, termPointer);
  }

  private native long defineFun(long pointer,
      String symbol,
      long[] boundVarPointers,
      long sortPointer,
      long termPointer,
      boolean global);

  /**
   * Define recursive function in the current context.
   *
   * SMT-LIB:
   * {@code
   * ( define-fun-rec <function_def> )
   * }
   *
   * @param symbol The name of the function.
   * @param boundVars The parameters to this function.
   * @param sort The sort of the return value of this function.
   * @param term The function body.
   * @return The function.
   */
  public Term defineFunRec(String symbol, Term[] boundVars, Sort sort, Term term)
  {
    return defineFunRec(symbol, boundVars, sort, term, false);
  }

  /**
   * Define recursive function.
   *
   * SMT-LIB:
   * {@code
   * ( define-fun-rec <function_def> )
   * }
   *
   * @param symbol The name of the function.
   * @param boundVars The parameters to this function.
   * @param sort The sort of the return value of this function.
   * @param term The function body.
   * @param global Determines whether this definition is global (i.e., persists
   *               when popping the context).
   * @return The function.
   */
  public Term defineFunRec(String symbol, Term[] boundVars, Sort sort, Term term, boolean global)
  {
    long[] boundVarPointers = Utils.getPointers(boundVars);
    long termPointer = defineFunRec(
        getPointer(), symbol, boundVarPointers, sort.getPointer(), term.getPointer(), global);
    return new Term(ctx, termPointer);
  }

  private native long defineFunRec(long pointer,
      String symbol,
      long[] boundVarPointers,
      long sortPointer,
      long termPointer,
      boolean global);

  /**
   * Define recursive function in the current context.
   *
   * SMT-LIB:
   * {@code
   * ( define-fun-rec <function_def> )
   * }
   *
   * Create parameter {@code fun} with {@link TermManager#mkConst(Sort)}.
   *
   * @param fun The sorted function.
   * @param boundVars The parameters to this function.
   * @param term The function body.
   * @return The function.
   */

  public Term defineFunRec(Term fun, Term[] boundVars, Term term)
  {
    return defineFunRec(fun, boundVars, term, false);
  }

  /**
   * Define recursive function.
   *
   * SMT-LIB:
   * {@code
   * ( define-fun-rec <function_def> )
   * }
   *
   * Create parameter {@code fun} with {@link TermManager#mkConst(Sort)}.
   *
   * @param fun The sorted function.
   * @param boundVars The parameters to this function.
   * @param term The function body.
   * @param global Determines whether this definition is global (i.e., persists
   *               when popping the context).
   * @return The function.
   */
  public Term defineFunRec(Term fun, Term[] boundVars, Term term, boolean global)
  {
    long[] boundVarPointers = Utils.getPointers(boundVars);
    long termPointer =
        defineFunRec(getPointer(), fun.getPointer(), boundVarPointers, term.getPointer(), global);
    return new Term(ctx, termPointer);
  }

  private native long defineFunRec(
      long pointer, long funPointer, long[] boundVarPointers, long termPointer, boolean global);

  /**
   * Define recursive functions in the current context.
   *
   * SMT-LIB:
   * {@code
   *   ( define-funs-rec ( <function_decl>^{n+1} ) ( <term>^{n+1} ) )
   * }
   *
   * Create elements of parameter {@code funs} with
   * {@link TermManager#mkConst(Sort)}.
   *
   * @param funs The sorted functions.
   * @param boundVars The list of parameters to the functions.
   * @param terms The list of function bodies of the functions.
   */
  public void defineFunsRec(Term[] funs, Term[][] boundVars, Term[] terms)
  {
    defineFunsRec(funs, boundVars, terms, false);
  }
  /**
   * Define recursive functions.
   *
   * SMT-LIB:
   * {@code
   *   ( define-funs-rec ( <function_decl>^{n+1} ) ( <term>^{n+1} ) )
   * }
   *
   * Create elements of parameter {@code funs} with
   * {@link TermManager#mkConst(Sort)}.
   *
   * @param funs The sorted functions.
   * @param boundVars The list of parameters to the functions.
   * @param terms The list of function bodies of the functions.
   * @param global Determines whether this definition is global (i.e., persists
   *               when popping the context).
   */
  public void defineFunsRec(Term[] funs, Term[][] boundVars, Term[] terms, boolean global)
  {
    long[] funPointers = Utils.getPointers(funs);
    long[][] boundVarPointers = Utils.getPointers(boundVars);
    long[] termPointers = Utils.getPointers(terms);
    defineFunsRec(getPointer(), funPointers, boundVarPointers, termPointers, global);
  }

  private native void defineFunsRec(long pointer,
      long[] funPointers,
      long[][] boundVarPointers,
      long[] termPointers,
      boolean global);

  /**
   * Get a list of input literals that are entailed by the current set of
   * assertions.
   *
   * SMT-LIB:
   * {@code
   * ( get-learned-literals )
   * }
   *
   * @api.note This method is experimental and may change in future versions.
   *
   * @return The list of learned literals.
   */
  public Term[] getLearnedLiterals()
  {
    long[] retPointers = getLearnedLiterals(getPointer());
    return Utils.getTerms(ctx, retPointers);
  }

  private native long[] getLearnedLiterals(long pointer);

  /**
   * Get a list of literals that are entailed by the current set of assertions.
   *
   * SMT-LIB:
   * {@code
   * ( get-learned-literals :type )
   * }
   *
   * @api.note This method is experimental and may change in future versions.
   *
   * @param type The type of learned literals to return
   * @return The list of learned literals.
   */
  public Term[] getLearnedLiterals(LearnedLitType type)
  {
    long[] retPointers = getLearnedLiterals(getPointer(), type.getValue());
    return Utils.getTerms(ctx, retPointers);
  }

  private native long[] getLearnedLiterals(long pointer, int type);

  /**
   * Get the list of asserted formulas.
   *
   * SMT-LIB:
   * {@code
   * ( get-assertions )
   * }
   *
   * @return The list of asserted formulas.
   */
  public Term[] getAssertions()
  {
    long[] retPointers = getAssertions(getPointer());
    return Utils.getTerms(ctx, retPointers);
  }

  private native long[] getAssertions(long pointer);

  /**
   * Get info from the solver.
   * SMT-LIB: {@code ( get-info <info_flag> ) }
   * @param flag The {@code get-info} flag.
   * @return The info.
   */
  public String getInfo(String flag)
  {
    return getInfo(getPointer(), flag);
  }

  private native String getInfo(long pointer, String flag);

  /**
   * Get the value of a given option.
   * SMT-LIB:
   * {@code
   * ( get-option <keyword> )
   * }
   * @param option The option for which the value is queried.
   * @return A string representation of the option value.
   */
  public String getOption(String option)
  {
    return getOption(getPointer(), option);
  }

  private native String getOption(long pointer, String option);

  /**
   * Get all option names that can be used with
   * {@link Solver#setOption(String, String)},
   * {@link Solver#getOption(String)} and
   * {@link Solver#getOptionInfo(String)}.
   * @return All option names.
   */
  public String[] getOptionNames()
  {
    return getOptionNames(getPointer());
  }

  private native String[] getOptionNames(long pointer);

  /**
   * Get some information about the given option.
   *
   * Check the {@link OptionInfo} class for more details on which information
   * is available.
   *
   * @param option The name of the option.
   * @return Information about the given option.
   */
  public OptionInfo getOptionInfo(String option)
  {
    long optionPointer = getOptionInfo(getPointer(), option);
    return new OptionInfo(ctx, optionPointer);
  }

  private native long getOptionInfo(long pointer, String option);

  /**
   * Get the set of unsat ("failed") assumptions.
   *
   * SMT-LIB:
   * {@code
   * ( get-unsat-assumptions )
   * }
   *
   * Requires to enable option {@code produce-unsat-assumptions}.
   *
   * @return The set of unsat assumptions.
   */
  public Term[] getUnsatAssumptions()
  {
    long[] retPointers = getUnsatAssumptions(getPointer());
    return Utils.getTerms(ctx, retPointers);
  }

  private native long[] getUnsatAssumptions(long pointer);

  /**
   * Get the unsatisfiable core.
   * SMT-LIB:
   * {@code
   * (get-unsat-core)
   * }
   * Requires to enable option {@code produce-unsat-cores}.
   *
   * @api.note In contrast to SMT-LIB, cvc5's API does not distinguish between
   *           named and unnamed assertions when producing an unsatisfiable
   *           core. Additionally, the API allows this option to be called after
   *           a check with assumptions. A subset of those assumptions may be
   *           included in the unsatisfiable core returned by this method.
   *
   * @return A set of terms representing the unsatisfiable core.
   */
  public Term[] getUnsatCore()
  {
    long[] retPointers = getUnsatCore(getPointer());
    return Utils.getTerms(ctx, retPointers);
  }

  private native long[] getUnsatCore(long pointer);

  /**
   * Get the lemmas used to derive unsatisfiability.
   * SMT-LIB:
   * {@code
   * (get-unsat-core-lemmas)
   * }
   * Requires the SAT proof unsat core mode, so to enable option {@code unsat-core-mode=sat-proof}
   *
   * @api.note This method is experimental and may change in future versions.
   *
   * @return A set of terms representing the lemmas used to derive
   * unsatisfiability.
   */
  public Term[] getUnsatCoreLemmas()
  {
    long[] retPointers = getUnsatCoreLemmas(getPointer());
    return Utils.getTerms(ctx, retPointers);
  }

  private native long[] getUnsatCoreLemmas(long pointer);

  /**
   * Get a difficulty estimate for an asserted formula. This method is
   * intended to be called immediately after any response to a checkSat.
   *
   * @api.note This method is experimental and may change in future versions.
   *
   * @return A map from (a subset of) the input assertions to a real value that.
   * is an estimate of how difficult each assertion was to solve. Unmentioned
   * assertions can be assumed to have zero difficulty.
   */
  public Map<Term, Term> getDifficulty()
  {
    Map<Long, Long> map = getDifficulty(getPointer());
    Map<Term, Term> ret = new HashMap<>();
    for (Map.Entry<Long, Long> entry : map.entrySet())
    {
      Term key = new Term(ctx, entry.getKey());
      Term value = new Term(ctx, entry.getValue());
      ret.put(key, value);
    }
    return ret;
  }

  private native Map<Long, Long> getDifficulty(long pointer);

  /**
   * Get a timeout core, which computes a subset of the current assertions that
   * cause a timeout. Note it does not require being proceeded by a call to
   * checkSat.
   *
   * SMT-LIB:
   * {@code
   * (get-timeout-core)
   * }
   *
   * @api.note This method is experimental and may change in future versions.
   *
   * @return The result of the timeout core computation. This is a pair
   * containing a result and a list of formulas. If the result is unknown
   * and the reason is timeout, then the list of formulas correspond to a
   * subset of the current assertions that cause a timeout in the specified
   * time {@code timeout-core-timeout}.
   * If the result is unsat, then the list of formulas correspond to an
   * unsat core for the current assertions. If the computation was terminated
   * by the connected terminator, the result is unknown with explanation
   * {@link UnknownExplanation#INTERRUPTED}, and the list of formulas is empty.
   * Otherwise, the result is sat, indicating that the current assertions are
   * satisfiable, and the list of formulas is empty.
   *
   * This method may make multiple checks for satisfiability internally, each
   * limited by the timeout value given by {@code timeout-core-timeout}.
   */
  public Pair<Result, Term[]> getTimeoutCore()
  {
    try
    {
      Pair<Long, long[]> pair = getTimeoutCore(getPointer());
      Result result = new Result(ctx, pair.first);
      Term[] terms = Utils.getTerms(ctx, pair.second);
      Pair<Result, Term[]> ret = new Pair<>(result, terms);
      return ret;
    }
    finally
    {
      checkTerminator();
    }
  }

  private native Pair<Long, long[]> getTimeoutCore(long pointer);

  /**
   * Get a timeout core, which computes a subset of the given assumptions that
   * cause a timeout when added to the current assertions. Note it does not
   * require being proceeded by a call to checkSat.
   *
   * SMT-LIB:
   * {@code
   * (get-timeout-core)
   * }
   *
   * @api.note This method is experimental and may change in future versions.
   *
   * @param assumptions The formulas to assume.
   * @return The result of the timeout core computation. This is a pair
   * containing a result and a list of formulas. If the result is unknown
   * and the reason is timeout, then the list of formulas correspond to a
   * subset of assumptions that cause a timeout when added to the current
   * assertions in the specified time {@code timeout-core-timeout}.
   * If the result is unsat, then the list of formulas plus the current
   * assertions correspond to an unsat core for the current assertions.
   * If the computation was terminated by the connected terminator, the result
   * is unknown with explanation {@link UnknownExplanation#INTERRUPTED}, and the
   * list of formulas is empty. Otherwise, the result is sat, indicating that
   * the given assumptions plus the current assertions are satisfiable, and the
   * list of formulas is empty.
   *
   * This method may make multiple checks for satisfiability internally, each
   * limited by the timeout value given by {@code timeout-core-timeout}.
   */
  public Pair<Result, Term[]> getTimeoutCoreAssuming(Term[] assumptions)
  {
    try
    {
      long[] pointers = Utils.getPointers(assumptions);
      Pair<Long, long[]> pair = getTimeoutCoreAssuming(getPointer(), pointers);
      // The native call may re-enter Java code (plugins, oracles), which may
      // release native objects whose wrappers are unreachable.
      Reference.reachabilityFence(assumptions);
      Result result = new Result(ctx, pair.first);
      Term[] terms = Utils.getTerms(ctx, pair.second);
      Pair<Result, Term[]> ret = new Pair<>(result, terms);
      return ret;
    }
    finally
    {
      checkTerminator();
    }
  }

  private native Pair<Long, long[]> getTimeoutCoreAssuming(long pointer, long[] assumptionPointers);

  /**
   * Get refutation proof for the most recent call to checkSat.
   *
   * SMT-LIB:
   * {@code
   * ( get-proof )
   * }
   *
   * Requires to enable option {@code produce-proofs}.
   *
   * @api.note This method is experimental and may change in future versions.
   *
   * @return A vector of proof nodes. This is equivalent to getProof
   * when c is FULL.
   */
  public Proof[] getProof()
  {
    return Utils.getProofs(ctx, getProof(getPointer()));
  }

  private native long[] getProof(long pointer);

  /**
   * Get a proof associated with the most recent call to checkSat.
   *
   * SMT-LIB:
   * {@code
   * ( get-proof :c)
   * }
   *
   * Requires to enable option {@code produce-proofs}.
   *
   * @api.note This method is experimental and may change in future versions.
   *
   * @param c The component of the proof to return
   * @return A vector of proof nodes.
   */
  public Proof[] getProof(ProofComponent c)
  {
    return Utils.getProofs(ctx, getProof(getPointer(), c.getValue()));
  }

  private native long[] getProof(long pointer, int c);

  /**
   * Prints a proof into a string with a slected proof format mode.
   * Other aspects of printing are taken from the solver options.
   *
   * @api.note This method is experimental and may change in future versions.
   *
   * @param proof A proof.
   * @return The proof printed in the current format.
   */
  public String proofToString(Proof proof)
  {
    return proofToString(getPointer(), proof.getPointer());
  }

  private native String proofToString(long pointer, long proofs);

  /**
   * Prints a proof into a string with a slected proof format mode.
   * Other aspects of printing are taken from the solver options.
   *
   * @api.note This method is experimental and may change in future versions.
   *
   * @param proof A proof.
   * @param format The proof format used to print the proof. Must be
   * `PROOF_FORMAT_NONE` if the proof is from a component other than
   * `PROOF_COMPONENT_FULL`.
   * @return The proof printed in the current format.
   */
  public String proofToString(Proof proof, ProofFormat format)
  {
    return proofToString(getPointer(), proof.getPointer(), format.getValue());
  }

  private native String proofToString(long pointer, long proofs, int format);

  /**
   * Prints a proof into a string with a slected proof format mode.
   * Other aspects of printing are taken from the solver options.
   *
   * @api.note This method is experimental and may change in future versions.
   *
   * @param proof A proof.
   * @param format The proof format used to print the proof. Must be
   * `PROOF_FORMAT_NONE` if the proof is from a component other than
   * `PROOF_COMPONENT_FULL`.
   * @param assertionNames Mapping between assertions and names, if they were
   * given by the user.  This is used by the Alethe proof format.
   * @return The proof printed in the current format.
   */
  public String proofToString(Proof proof, ProofFormat format, Map assertionNames)
  {
    return proofToString(getPointer(), proof.getPointer(), format.getValue(), assertionNames);
  }

  private native String proofToString(long pointer, long proofs, int format, Map assertionNames);

  /**
   * Get the value of the given term in the current model.
   *
   * SMT-LIB:
   * {@code
   * ( get-value ( <term> ) )
   * }
   *
   * @param term The term for which the value is queried.
   * @return The value of the given term.
   */
  public Term getValue(Term term)
  {
    try
    {
      long termPointer = getValue(getPointer(), term.getPointer());
      return new Term(ctx, termPointer);
    }
    finally
    {
      checkTerminator();
    }
  }

  private native long getValue(long pointer, long termPointer);

  /**
   * Get the values of the given terms in the current model.
   *
   * SMT-LIB:
   * {@code
   * ( get-value ( <term>+ ) )
   * }
   *
   * @param terms The terms for which the value is queried.
   * @return The values of the given terms.
   */
  public Term[] getValue(Term[] terms)
  {
    try
    {
      long[] pointers = Utils.getPointers(terms);
      long[] retPointers = getValue(getPointer(), pointers);
      return Utils.getTerms(ctx, retPointers);
    }
    finally
    {
      checkTerminator();
    }
  }

  private native long[] getValue(long pointer, long[] termPointers);

  /**
   * Get the domain elements of uninterpreted sort s in the current model.
   *
   * The current model interprets {@code s} as the finite sort whose domain
   * elements are given in the return value of this method.
   *
   * @param s The uninterpreted sort in question.
   * @return The domain elements of {@code s} in the current model.
   */
  public Term[] getModelDomainElements(Sort s)
  {
    long[] pointers = getModelDomainElements(getPointer(), s.getPointer());
    return Utils.getTerms(ctx, pointers);
  }

  private native long[] getModelDomainElements(long pointer, long sortPointer);

  /**
   * This returns false if the model value of free constant {@code v} was not
   * essential for showing the satisfiability of the last call to
   * {@link Solver#checkSat()} using the current model. This method will only
   * return false (for any {@code v}) if the option {@code model-cores} has
   * been set.
   *
   * @api.note This method is experimental and may change in future versions.
   *
   * @param v The term in question.
   * @return True if v is a model core symbol.
   */
  public boolean isModelCoreSymbol(Term v)
  {
    return isModelCoreSymbol(getPointer(), v.getPointer());
  }

  private native boolean isModelCoreSymbol(long pointer, long termPointer);

  /**
   * Get the model
   *
   * SMT-LIB:
   * {@code
   * ( get-model )
   * }
   *
   * Requires to enable option {@code produce-models}.
   *
   * @api.note This method is experimental and may change in future versions.
   *
   * @param sorts The list of uninterpreted sorts that should be printed in the.
   *              model.
   * @param vars The list of free constants that should be printed in the.
   *             model. A subset of these may be printed based on
   *             {@link Solver#isModelCoreSymbol(Term)}.
   * @return A string representing the model.
   */
  public String getModel(Sort[] sorts, Term[] vars)
  {
    long[] sortPointers = Utils.getPointers(sorts);
    long[] varPointers = Utils.getPointers(vars);
    return getModel(getPointer(), sortPointers, varPointers);
  }

  private native String getModel(long pointer, long[] sortPointers, long[] varPointers);

  /**
   * Do quantifier elimination.
   *
   * SMT-LIB:
   * {@code
   * ( get-qe <q> )
   * }
   *
   * Quantifier Elimination is only complete for logics such as LRA,
   * LIA and BV.
   *
   * The formula {@code q} must not contain free variables, i.e., variables
   * constructed via {@link TermManager#mkVar(Sort)} that are not bound by a
   * quantifier in {@code q}. The symbols {@code y1...yn} should be free
   * constants constructed via {@link TermManager#mkConst(Sort)}. An exception
   * is thrown if {@code q} contains free variables.
   *
   * @api.note This method is experimental and may change in future versions.
   *
   * @param q A quantified formula of the form:
   *          {@code Q x1...xn. P( x1...xn, y1...yn )}
   *          where {@code P( x1...xn, y1...yn )} is a quantifier-free formula.
   * @return A formula {@code ret} such that, given the current set of formulas
   *         {@code A} asserted to this solver:
   *         - {@code ( A && q )} and {@code ( A && ret )} are equivalent
   *         - {@code ret} is quantifier-free formula containing only free
   *           constants in {@code y1...yn}.
   */
  public Term getQuantifierElimination(Term q)
  {
    try
    {
      long termPointer = getQuantifierElimination(getPointer(), q.getPointer());
      return new Term(ctx, termPointer);
    }
    finally
    {
      checkTerminator();
    }
  }

  private native long getQuantifierElimination(long pointer, long qPointer);

  /**
   * Do partial quantifier elimination, which can be used for incrementally
   * computing the result of a quantifier elimination.
   *
   * SMT-LIB:
   * {@code
   * ( get-qe-disjunct <q> )
   * }
   *
   * Quantifier Elimination is only complete for logics such as LRA,
   * LIA and BV.
   *
   * The formula {@code q} must not contain free variables, i.e., variables
   * constructed via {@link TermManager#mkVar(Sort)} that are not bound by a
   * quantifier in {@code q}. The symbols {@code y1...yn} should be free
   * constants constructed via {@link TermManager#mkConst(Sort)}. An exception
   * is thrown if {@code q} contains free variables.
   *
   * @api.note This method is experimental and may change in future versions.
   *
   * @param q A quantified formula of the form:
   *          {@code Q x1...xn. P( x1...xn, y1...yn )}
   *          where {@code P( x1...xn, y1...yn )} is a quantifier-free formula.
   * @return A formula ret such that, given the current set of formulas A
   *         asserted to this solver:
   *           - {@code (A ^ q) => (A ^ ret)} if {@code Q} is forall or
   *             {@code (A ^ ret) => (A ^ q)} if {@code Q} is exists,
   *           - ret is quantifier-free formula containing only free constants
   *             in {@code y1...yn},
   *           - If Q is exists, let {@code A && Q_n} be the formula
   *               {@code A && ~(ret && Q_1) && ... && ~(ret && Q_n)}
   *             where for each {@code i=1,...n}, formula {@code ret && Q_i}
   *             is the result of calling
   *             {@link Solver#getQuantifierEliminationDisjunct(Term)}
   *             for {@code q} with the set of assertions
   *             {@code A && Q_{i-1}}. Similarly, if {@code Q} is forall, then
   *             let {@code A && Q_n} be
   *             {@code A && (ret && Q_1) && ... && (ret&& Q_n) }
   *             where {@code ret && Q_i} is the same as above. In either case,
   *             we have that {@code ret && Q_j} will eventually be true or
   *             false, for some finite {@code j}.
   */
  public Term getQuantifierEliminationDisjunct(Term q)
  {
    try
    {
      long termPointer = getQuantifierEliminationDisjunct(getPointer(), q.getPointer());
      return new Term(ctx, termPointer);
    }
    finally
    {
      checkTerminator();
    }
  }

  private native long getQuantifierEliminationDisjunct(long pointer, long qPointer);

  /**
   * When using separation logic, this sets the location sort and the
   * datatype sort to the given ones. This method should be invoked exactly
   * once, before any separation logic constraints are provided.
   *
   * @api.note This method is experimental and may change in future versions.
   *
   * @param locSort The location sort of the heap.
   * @param dataSort The data sort of the heap.
   */
  public void declareSepHeap(Sort locSort, Sort dataSort)
  {
    declareSepHeap(getPointer(), locSort.getPointer(), dataSort.getPointer());
  }

  private native void declareSepHeap(long pointer, long locSortPointer, long dataSortPointer);

  /**
   * When using separation logic, obtain the term for the heap.
   *
   * @api.note This method is experimental and may change in future versions.
   *
   * @return The term for the heap.
   */
  public Term getValueSepHeap()
  {
    long termPointer = getValueSepHeap(getPointer());
    return new Term(ctx, termPointer);
  }

  private native long getValueSepHeap(long pointer);

  /**
   * When using separation logic, obtain the term for nil.
   *
   * @api.note This method is experimental and may change in future versions.
   *
   * @return The term for nil.
   */
  public Term getValueSepNil()
  {
    long termPointer = getValueSepNil(getPointer());
    return new Term(ctx, termPointer);
  }

  private native long getValueSepNil(long pointer);

  /**
   * Declare a symbolic pool of terms with the given initial value.
   *
   * SMT-LIB:
   * {@code
   * ( declare-pool <symbol> <sort> ( <term>* ) )
   * }
   *
   * @api.note This method is experimental and may change in future versions.
   *
   * @param symbol The name of the pool.
   * @param sort The sort of the elements of the pool.
   * @param initValue The initial value of the pool.
   * @return The pool.
   */
  public Term declarePool(String symbol, Sort sort, Term[] initValue)
  {
    long[] termPointers = Utils.getPointers(initValue);
    long termPointer = declarePool(getPointer(), symbol, sort.getPointer(), termPointers);
    return new Term(ctx, termPointer);
  }

  private native long declarePool(
      long pointer, String symbol, long sortPointer, long[] termPointers);

  /**
   * Declare an oracle function with reference to an implementation.
   *
   * Oracle functions have a different semantics with respect to ordinary
   * declared functions. In particular, for an input to be satisfiable,
   * its oracle functions are implicitly universally quantified.
   *
   * This method is used in part for implementing this command:
   *
   * {@code
   * (declare-oracle-fun <sym> (<sort>*) <sort> <sym>)
   * }
   *
   *
   * In particular, the above command is implemented by constructing a
   * function over terms that wraps a call to binary sym via a text interface.
   *
   * @api.note This method is experimental and may change in future versions.
   *
   * @param symbol The name of the oracle
   * @param sorts The sorts of the parameters to this function
   * @param sort The sort of the return value of this function
   * @param oracle An object that implements the oracle interface.
   * @return The oracle function
   */
  public Term declareOracleFun(String symbol, Sort[] sorts, Sort sort, IOracle oracle)
  {
    long[] sortPointers = Utils.getPointers(sorts);
    OracleBridge bridge = new OracleBridge(ctx, oracle);
    callbacks.add(bridge);
    long termPointer =
        declareOracleFun(getPointer(), symbol, sortPointers, sort.getPointer(), bridge);
    return new Term(ctx, termPointer);
  }

  private native long declareOracleFun(
      long pointer, String symbol, long[] sortPointers, long sortPointer, OracleBridge oracle);

  /**
   * Bridges native oracle calls to an {@link IOracle}.
   *
   * <p>Native code exchanges raw pointers with this class, so that the
   * {@link Term} wrappers are created here, in the context of the solver's
   * term manager.</p>
   */
  private static final class OracleBridge
  {
    private final NativeContext ctx;
    private final IOracle oracle;

    OracleBridge(NativeContext ctx, IOracle oracle)
    {
      this.ctx = ctx;
      this.oracle = oracle;
    }

    /**
     * Called from native code.
     *
     * @param pointers The native pointers of the arguments; ownership is
     *                 transferred to the created wrappers.
     * @return The native pointer of the result, which native code copies
     *         before any further Java code can run on this thread.
     */
    long apply(long[] pointers) throws CVC5ApiException
    {
      return oracle.apply(Utils.getTerms(ctx, pointers)).getPointer();
    }
  }

  /**
   * Add plugin to this solver. Its callbacks will be called throughout the
   * lifetime of this solver.
   *
   * @param p The plugin to add to this solver.
   */
  public void addPlugin(AbstractPlugin p)
  {
    callbacks.add(p);
    addPlugin(getPointer(), p.getTermManager().getPointer(), p);
  }

  private native void addPlugin(long pointer, long termManagerPointer, AbstractPlugin p);

  /**
   * Connect a terminator to this solver, which is called periodically during
   * queries to determine whether the current query should be terminated.
   * See {@link ITerminator} for details.
   * <p>
   * Only one terminator can be connected at a time, connecting a terminator
   * disconnects the previously connected terminator.
   *
   * @api.note This method is experimental and may change in future versions.
   *
   * @param terminator The terminator to connect, or null to disconnect the
   *                   currently connected terminator.
   */
  public void setTerminator(ITerminator terminator)
  {
    TerminatorWrapper wrapper = terminator == null ? null : new TerminatorWrapper(terminator);
    setTerminator(getPointer(), wrapper);
    terminatorWrapper = wrapper;
  }

  private native void setTerminator(long pointer, TerminatorWrapper wrapper);

  /**
   * Wrapper of the connected terminator, which is called from the native code.
   * Exceptions thrown by the terminator are remembered, and rethrown by the
   * method that executed the query.
   */
  private static class TerminatorWrapper
  {
    TerminatorWrapper(ITerminator terminator)
    {
      this.terminator = terminator;
    }

    /**
     * Called from the native code to determine whether the current query
     * should be terminated.
     *
     * @return True to terminate the current query.
     */
    boolean terminate()
    {
      try
      {
        return terminator.terminate();
      }
      catch (Throwable t)
      {
        exception = t;
        return true;
      }
    }

    /** The wrapped terminator. */
    private final ITerminator terminator;
    /** The exception thrown by the terminator, if any. */
    private Throwable exception;
  }

  /**
   * Rethrow the exception thrown by the connected terminator during the last
   * query, if any. Must be called by all methods that execute queries when the
   * query returns, also if it threw an exception (i.e., in a finally block).
   * The exception of the terminator then replaces the exception of the query.
   */
  void checkTerminator()
  {
    TerminatorWrapper wrapper = terminatorWrapper;
    if (wrapper != null && wrapper.exception != null)
    {
      Throwable t = wrapper.exception;
      wrapper.exception = null;
      if (t instanceof RuntimeException)
      {
        throw (RuntimeException) t;
      }
      if (t instanceof Error)
      {
        throw (Error) t;
      }
      throw new RuntimeException(t);
    }
  }

  /**
   * Pop a level from the assertion stack.
   *
   * SMT-LIB:
   * {@code
   * ( pop <numeral> )
   * }
   *
   * @throws CVC5ApiException on error
   */
  public void pop() throws CVC5ApiException
  {
    pop(1);
  }

  /**
   * Pop (a) level(s) from the assertion stack.
   *
   * SMT-LIB:
   * {@code
   * ( pop <numeral> )
   * }
   *
   * @param nscopes The number of levels to pop.
   * @throws CVC5ApiException on error
   */
  public void pop(int nscopes) throws CVC5ApiException
  {
    Utils.validateUnsigned(nscopes, "nscopes");
    pop(getPointer(), nscopes);
  }

  private native void pop(long pointer, int nscopes);

  /**
   * Get an interpolant.
   *
   * <p>
   * Given that {@code A->B} is valid,
   * this function determines a term {@code I}
   * over the shared variables of {@code A} and
   * {@code B},
   * such that {@code A->I} and {@code I->B}
   * are valid. {@code A} is the current set of
   * assertions and {@code B} is the conjecture, given as {@code conj}.
   * </p>
   *
   * SMT-LIB:
   * {@code
   * ( get-interpolant <symbol> <conj> )
   * }
   *
   * @api.note In SMT-LIB, {@code <symbol>} assigns a symbol to the interpolant.
   *
   * @api.note Requires option {@code produce-interpolants} to be set to a mode
   * different from {@code none}.
   *
   * @api.note This method is experimental and may change in future versions.
   *
   * @param conj The conjecture term.
   * @return The interpolant, if an interpolant exists, else the null term.
   */
  public Term getInterpolant(Term conj)
  {
    try
    {
      long interpolPtr = getInterpolant(getPointer(), conj.getPointer());
      // The native call may re-enter Java code (plugins, oracles), which may
      // release native objects whose wrappers are unreachable.
      Reference.reachabilityFence(conj);
      return new Term(ctx, interpolPtr);
    }
    finally
    {
      checkTerminator();
    }
  }

  private native long getInterpolant(long pointer, long conjPointer);

  /**
   * Get an interpolant.
   *
   * <p>
   * Given that {@code A->B} is valid,
   * this function determines a term {@code I},
   * over the shared variables of {@code A} and
   * {@code B},
   * with respect to a given grammar, such
   * that {@code A->I} and {@code I->B} are valid, if such a term exits.
   * {@code A} is the current set of assertions and {@code B} is the
   * conjecture, given as {@code conj}.
   * </p>
   *
   * SMT-LIB:
   * {@code
   * ( get-interpolant <symbol> <conj> <g> )
   * }
   *
   * @api.note In SMT-LIB, {@code <symbol>} assigns a symbol to the interpolant.
   *
   * @api.note Requires option {@code produce-interpolants} to be set to a mode
   * different from {@code none}.
   *
   * @api.note This method is experimental and may change in future versions.
   *
   * @param conj The conjecture term.
   * @param grammar The grammar for the interpolant {@code I}.
   * @return The interpolant, if an interpolant exists, else the null term.
   */
  public Term getInterpolant(Term conj, Grammar grammar)
  {
    try
    {
      long interpolPtr = getInterpolant(getPointer(), conj.getPointer(), grammar.getPointer());
      // The native call may re-enter Java code (plugins, oracles), which may
      // release native objects whose wrappers are unreachable.
      Reference.reachabilityFence(conj);
      Reference.reachabilityFence(grammar);
      return new Term(ctx, interpolPtr);
    }
    finally
    {
      checkTerminator();
    }
  }

  private native long getInterpolant(long pointer, long conjPointer, long grammarPointer);

  /**
   * Get the next interpolant.
   *
   * Can only be called immediately after a successful call to
   * {@code get-interpolant} or {@code get-interpolant-next}. Is guaranteed to
   * produce a syntactically different interpolant wrt the last returned
   * interpolant if successful.
   *
   * SMT-LIB:
   * {@code
   *     (get-interpolant-next)
   * }
   *
   * Requires to enable incremental mode, and option
   * {@code produce-interpolants} to be set to a mode different from
   * {@code none}.
   *
   * @api.note This method is experimental and may change in future versions.
   *
   * @return A Term I such that {@code A->I} and {@code I->B} are valid,
   *         where {@code A} is the current set of assertions and {@code B}
   *         is given in the input by conj on the last call to getInterpolant,
   *         or the null term if such a term cannot be found.
   */
  public Term getInterpolantNext()
  {
    try
    {
      long interpolPtr = getInterpolantNext(getPointer());
      return new Term(ctx, interpolPtr);
    }
    finally
    {
      checkTerminator();
    }
  }

  private native long getInterpolantNext(long pointer);

  /**
   * Get an abduct.
   *
   * SMT-LIB:
   * {@code
   * ( get-abduct <conj> )
   * }
   * Requires enabling option {@code produce-abducts}.
   *
   * @api.note This method is experimental and may change in future versions.
   *
   * @param conj The conjecture term.
   * @return A term {@code C} such that {@code A && C} is satisfiable, and
   *         {@code A && ~B && C} is unsatisfiable, where {@code A} is the
   *         current set of assertions and {@code B} is given in the input by
   *         {@code conj}, or the null term if such a term cannot be found.
   */
  public Term getAbduct(Term conj)
  {
    try
    {
      long abdPtr = getAbduct(getPointer(), conj.getPointer());
      // The native call may re-enter Java code (plugins, oracles), which may
      // release native objects whose wrappers are unreachable.
      Reference.reachabilityFence(conj);
      return new Term(ctx, abdPtr);
    }
    finally
    {
      checkTerminator();
    }
  }

  private native long getAbduct(long pointer, long conjPointer);
  /**
   * Get an abduct.
   *
   * SMT-LIB:
   * {@code
   * ( get-abduct <conj> <g> )
   * }
   *
   * Requires enabling option {@code produce-abducts}.
   *
   * @api.note This method is experimental and may change in future versions.
   *
   * @param conj The conjecture term.
   * @param grammar The grammar for the abduct {@code C}.
   * @return A term {@code C} such that {@code A && C} is satisfiable, and
   *         {@code A && ~B && C} is unsatisfiable, where {@code A} is the
   *         current set of assertions and {@code B} is given in the input by
   *         {@code conj}, or the null term if such a term cannot be found.
   */
  public Term getAbduct(Term conj, Grammar grammar)
  {
    try
    {
      long abdPtr = getAbduct(getPointer(), conj.getPointer(), grammar.getPointer());
      // The native call may re-enter Java code (plugins, oracles), which may
      // release native objects whose wrappers are unreachable.
      Reference.reachabilityFence(conj);
      Reference.reachabilityFence(grammar);
      return new Term(ctx, abdPtr);
    }
    finally
    {
      checkTerminator();
    }
  }

  private native long getAbduct(long pointer, long conjPointer, long grammarPointer);

  /**
   * Get the next abduct. Can only be called immediately after a successful
   * call to get-abduct or get-abduct-next. Is guaranteed to produce a
   * syntactically different abduct wrt the last returned abduct if successful.
   * SMT-LIB:
   * {@code
   * ( get-abduct-next )
   * }
   * Requires enabling incremental mode and option {@code produce-abducts}.
   *
   * @api.note This method is experimental and may change in future versions.
   *
   * @return A term C such that A^C is satisfiable, and A^~B^C is.
   *         unsatisfiable, where A is the current set of assertions and B is
   *         given in the input by conj in the last call to getAbduct, or the
   *         null term if such a term cannot be found.
   */
  public Term getAbductNext()
  {
    try
    {
      long abdPtr = getAbductNext(getPointer());
      return new Term(ctx, abdPtr);
    }
    finally
    {
      checkTerminator();
    }
  }

  private native long getAbductNext(long pointer);

  /**
   * Block the current model.
   *
   * Can be called only if immediately preceded by a SAT or INVALID query.
   *
   * SMT-LIB:
   * {@code
   * ( block-model )
   * }
   *
   * Requires enabling option {@code produce-models}.
   *
   * @api.note This method is experimental and may change in future versions.
   *
   * @param mode The mode to use for blocking.
   */
  public void blockModel(BlockModelsMode mode)
  {
    blockModel(getPointer(), mode.getValue());
  }

  private native void blockModel(long pointer, int modeValue);

  /**
   * Block the current model values of (at least) the values in terms.
   *
   * Can be called only if immediately preceded by a SAT query.
   *
   * SMT-LIB:
   * {@code
   * ( block-model-values ( <terms>+ ) )
   * }
   *
   * Requires enabling option {@code produce-models}.
   *
   * @api.note This method is experimental and may change in future versions.
   *
   * @param terms The model values to block.
   */
  public void blockModelValues(Term[] terms)
  {
    long[] pointers = Utils.getPointers(terms);
    blockModelValues(getPointer(), pointers);
  }

  private native void blockModelValues(long pointer, long[] termPointers);

  /**
   * Get a string that contains information about all instantiations made by
   * the quantifiers module.
   *
   * @api.note This method is experimental and may change in future versions.
   *
   * @return The string representing the information about all instantiations.
   */
  public String getInstantiations()
  {
    return getInstantiations(getPointer());
  }

  private native String getInstantiations(long pointer);

  /**
   * Push a level to the assertion stack.
   *
   * SMT-LIB:
   * {@code
   * ( push <numeral> )
   * }
   *
   * @throws CVC5ApiException on error
   */
  public void push() throws CVC5ApiException
  {
    push(1);
  }

  /**
   * Push (a) level(s) to the assertion stack.
   *
   * SMT-LIB:
   * {@code
   * ( push <numeral> )
   * }
   *
   * @param nscopes The number of levels to push.
   * @throws CVC5ApiException on error
   */
  public void push(int nscopes) throws CVC5ApiException
  {
    Utils.validateUnsigned(nscopes, "nscopes");
    push(getPointer(), nscopes);
  }

  private native void push(long pointer, int nscopes);

  /**
   * Remove all assertions.
   *
   * SMT-LIB:
   * {@code
   * ( reset-assertions )
   * }
   */
  public void resetAssertions()
  {
    resetAssertions(getPointer());
  }

  private native void resetAssertions(long pointer);

  /**
   * Set info.
   *
   * SMT-LIB:
   * {@code
   * ( set-info <attribute> )
   * }
   *
   * @param keyword The info flag.
   * @param value The value of the info flag.
   * @throws CVC5ApiException on error
   */
  public void setInfo(String keyword, String value) throws CVC5ApiException
  {
    setInfo(getPointer(), keyword, value);
  }

  private native void setInfo(long pointer, String keyword, String value) throws CVC5ApiException;

  /**
   * Set logic.
   *
   * SMT-LIB:
   * {@code
   * ( set-logic <symbol> )
   * }
   *
   * @param logic The logic to set.
   * @throws CVC5ApiException on error
   */
  public void setLogic(String logic) throws CVC5ApiException
  {
    setLogic(getPointer(), logic);
  }

  private native void setLogic(long pointer, String logic) throws CVC5ApiException;

  /**
   * Is logic set? Returns whether we called setLogic yet for this solver.
   *
   * @return whether we called setLogic yet for this solver.
   */
  public boolean isLogicSet()
  {
    return isLogicSet(getPointer());
  }

  private native boolean isLogicSet(long pointer);

  /**
   * Get the logic set the solver.
   *
   * @api.note Asserts isLogicSet().
   *
   * @return The logic used by the solver.
   * @throws CVC5ApiException on error
   */
  public String getLogic() throws CVC5ApiException
  {
    return getLogic(getPointer());
  }

  private native String getLogic(long pointer) throws CVC5ApiException;

  /**
   * Set option.
   *
   * SMT-LIB:
   * {@code
   *   ( set-option <option> )
   * }
   *
   * @param option The option name.
   * @param value The option value.
   */
  public void setOption(String option, String value)
  {
    setOption(getPointer(), option, value);
  }

  private native void setOption(long pointer, String option, String value);

  /**
   * Append {@code symbol} to the current list of universal variables.
   *
   * SyGuS v2:
   * {@code
   *   ( declare-var <symbol> <sort> )
   * }
   *
   * @param sort The sort of the universal variable.
   * @param symbol The name of the universal variable.
   * @return The universal variable.
   */
  public Term declareSygusVar(String symbol, Sort sort)
  {
    long termPointer = declareSygusVar(getPointer(), symbol, sort.getPointer());
    return new Term(ctx, termPointer);
  }

  private native long declareSygusVar(long pointer, String symbol, long sortPointer);

  /**
   * Synthesize n-ary function.
   *
   * SyGuS v2:
   * {@code
   *   ( synth-fun <symbol> ( <boundVars>* ) <sort> )
   * }
   *
   * @param symbol The name of the function.
   * @param boundVars The parameters to this function.
   * @param sort The sort of the return value of this function.
   * @return The function.
   */
  public Term synthFun(String symbol, Term[] boundVars, Sort sort)
  {
    long[] boundVarPointers = Utils.getPointers(boundVars);
    long termPointer = synthFun(getPointer(), symbol, boundVarPointers, sort.getPointer());
    return new Term(ctx, termPointer);
  }

  private native long synthFun(
      long pointer, String symbol, long[] boundVarPointers, long sortPointer);

  /**
   * Synthesize n-ary function following specified syntactic constraints.
   *
   * SyGuS v2:
   * {@code
   *   ( synth-fun <symbol> ( <boundVars>* ) <sort> <g> )
   * }
   *
   * @param symbol The name of the function.
   * @param boundVars The parameters to this function.
   * @param sort The sort of the return value of this function.
   * @param grammar The syntactic constraints.
   * @return The function.
   */
  public Term synthFun(String symbol, Term[] boundVars, Sort sort, Grammar grammar)
  {
    long[] boundVarPointers = Utils.getPointers(boundVars);
    long termPointer =
        synthFun(getPointer(), symbol, boundVarPointers, sort.getPointer(), grammar.getPointer());
    return new Term(ctx, termPointer);
  }

  private native long synthFun(
      long pointer, String symbol, long[] boundVarPointers, long sortPointer, long grammarPointer);

  /**
   * Add a forumla to the set of Sygus constraints.
   *
   * SyGuS v2:
   * {@code
   *   ( constraint <term> )
   * }
   *
   * @param term The formula to add as a constraint.
   */
  public void addSygusConstraint(Term term)
  {
    addSygusConstraint(getPointer(), term.getPointer());
  }

  private native void addSygusConstraint(long pointer, long termPointer);

  /**
   * Get the list of sygus constraints.
   *
   * @return The list of sygus constraints.
   */
  public Term[] getSygusConstraints()
  {
    long[] retPointers = getSygusConstraints(getPointer());
    return Utils.getTerms(ctx, retPointers);
  }

  private native long[] getSygusConstraints(long pointer);

  /**
   * Add a forumla to the set of Sygus assumptions.
   *
   * SyGuS v2:
   * {@code
   *   ( assume <term> )
   * }
   *
   * @param term The formula to add as an assumption.
   */
  public void addSygusAssume(Term term)
  {
    addSygusAssume(getPointer(), term.getPointer());
  }

  private native void addSygusAssume(long pointer, long termPointer);

  /**
   * Get the list of sygus assumptions.
   *
   * @return The list of sygus assumptions.
   */
  public Term[] getSygusAssumptions()
  {
    long[] retPointers = getSygusAssumptions(getPointer());
    return Utils.getTerms(ctx, retPointers);
  }

  private native long[] getSygusAssumptions(long pointer);

  /**
   * Add a set of Sygus constraints to the current state that correspond to an
   * invariant synthesis problem.
   *
   * SyGuS v2:
   * {@code
   *   ( inv-constraint <inv> <pre> <trans> <post> )
   * }
   *
   * @param inv The function-to-synthesize.
   * @param pre The pre-condition.
   * @param trans The transition relation.
   * @param post The post-condition.
   */
  public void addSygusInvConstraint(Term inv, Term pre, Term trans, Term post)
  {
    addSygusInvConstraint(
        getPointer(), inv.getPointer(), pre.getPointer(), trans.getPointer(), post.getPointer());
  }

  private native void addSygusInvConstraint(
      long pointer, long invPointer, long prePointer, long transPointer, long postPointer);

  /**
   * Try to find a solution for the synthesis conjecture corresponding to the
   * current list of functions-to-synthesize, universal variables and
   * constraints.
   *
   * SyGuS v2:
   * {@code
   *   ( check-synth )
   * }
   *
   * @return The result of the check, which is "solution" if the check found a.
   *         solution in which case solutions are available via
   *         getSynthSolutions, "no solution" if it was determined there is no
   *         solution, or "unknown" otherwise.
   */
  public SynthResult checkSynth()
  {
    try
    {
      long resultPointer = checkSynth(getPointer());
      return new SynthResult(ctx, resultPointer);
    }
    finally
    {
      checkTerminator();
    }
  }

  private native long checkSynth(long pointer);

  /**
   * Try to find a next solution for the synthesis conjecture corresponding to
   * the current list of functions-to-synthesize, universal variables and
   * constraints. Must be called immediately after a successful call to
   * {@code check-synth} or {@code check-synth-next}.
   *
   * @api.note Requires incremental mode.
   *
   * SyGuS v2:
   * {@code
   *   ( check-synth-next )
   * }
   *
   * @return The result of the check, which is "solution" if the check found a
   *         solution in which case solutions are available via
   *         getSynthSolutions, "no solution" if it was determined there is no
   *         solution, or "unknown" otherwise.
   */
  public SynthResult checkSynthNext()
  {
    try
    {
      long resultPointer = checkSynthNext(getPointer());
      return new SynthResult(ctx, resultPointer);
    }
    finally
    {
      checkTerminator();
    }
  }

  private native long checkSynthNext(long pointer);

  /**
   * Get the synthesis solution of the given term.
   *
   * This method should be called immediately after the solver answers unsat
   * for sygus input.
   *
   * @param term The term for which the synthesis solution is queried.
   * @return The synthesis solution of the given term.
   */
  public Term getSynthSolution(Term term)
  {
    long termPointer = getSynthSolution(getPointer(), term.getPointer());
    return new Term(ctx, termPointer);
  }

  private native long getSynthSolution(long pointer, long termPointer);

  /**
   * Get the synthesis solutions of the given terms.
   *
   * This method should be called immediately after the solver answers unsat
   * for sygus input.
   *
   * @param terms The terms for which the synthesis solutions is queried.
   * @return The synthesis solutions of the given terms.
   */
  public Term[] getSynthSolutions(Term[] terms)
  {
    long[] termPointers = Utils.getPointers(terms);
    long[] retPointers = getSynthSolutions(getPointer(), termPointers);
    return Utils.getTerms(ctx, retPointers);
  }

  private native long[] getSynthSolutions(long pointer, long[] termPointers);

  /**
   * Find a target term of interest using sygus enumeration, with no provided
   * grammar.
   *
   * The solver will infer which grammar to use in this call, which by default
   * will be the grammars specified by the function(s)-to-synthesize in the
   * current context.
   *
   * SyGuS v2:
   * {@code
   *     (find-synth :target)
   * }
   *
   * @param fst The identifier specifying what kind of term to find
   * @return The result of the find, which is the null term if this call failed.
   *
   * @api.note This method is experimental and may change in future versions.
   */
  public Term findSynth(FindSynthTarget fst)
  {
    try
    {
      long termPointer = findSynth(getPointer(), fst.getValue());
      return new Term(ctx, termPointer);
    }
    finally
    {
      checkTerminator();
    }
  }
  private native long findSynth(long pointer, int fst);

  /**
   * Find a target term of interest using sygus enumeration with a provided
   * grammar.
   *
   * SyGuS v2:
   * {@code
   *     (find-synth :target G)
   * }
   *
   * @param fst The identifier specifying what kind of term to find
   * @param grammar The grammar for the term
   * @return The result of the find, which is the null term if this call failed.
   *
   * @api.note This method is experimental and may change in future versions.
   */
  public Term findSynth(FindSynthTarget fst, Grammar grammar)
  {
    try
    {
      long termPointer = findSynth(getPointer(), fst.getValue(), grammar.getPointer());
      // The native call may re-enter Java code (plugins, oracles), which may
      // release native objects whose wrappers are unreachable.
      Reference.reachabilityFence(grammar);
      return new Term(ctx, termPointer);
    }
    finally
    {
      checkTerminator();
    }
  }
  private native long findSynth(long pointer, int fst, long grammarPointer);

  /**
   * Try to find a next target term of interest using sygus enumeration. Must
   * be called immediately after a successful call to find-synth or
   * find-synth-next.
   *
   * SyGuS v2:
   * {@code
   *     (find-synth-next)
   * }
   *
   * @return The result of the find, which is the null term if this call failed.
   *
   * @api.note This method is experimental and may change in future versions.
   */
  public Term findSynthNext()
  {
    try
    {
      long termPointer = findSynthNext(getPointer());
      return new Term(ctx, termPointer);
    }
    finally
    {
      checkTerminator();
    }
  }

  private native long findSynthNext(long pointer);

  /**
   * Get a snapshot of the current state of the statistic values of this
   * solver. The returned object will not change when the solver is used
   * again. Like every object derived from a term manager, it is released
   * when that term manager is closed, see {@link TermManager#close()}.
   * @return A snapshot of the current state of the statistic values.
   */
  public Statistics getStatistics()
  {
    long statisticsPointer = getStatistics(getPointer());
    return new Statistics(ctx, statisticsPointer);
  }

  private native long getStatistics(long pointer);

  /**
   * Get a string representation of the version of this solver.
   * @return The version string.
   */
  public String getVersion()
  {
    return getVersion(getPointer());
  }

  private native String getVersion(long pointer);
}
