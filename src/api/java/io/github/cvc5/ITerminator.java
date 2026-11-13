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
 *
 * ITerminator interface for terminating queries of a solver.
 */

package io.github.cvc5;

/**
 * A terminator, which allows to terminate queries of a solver.
 *
 * A terminator is connected to a solver via
 * {@link Solver#setTerminator(ITerminator)}. While the solver executes a query
 * (e.g., {@link Solver#checkSat()}), it periodically calls
 * {@link #terminate()} to determine whether the query should be terminated.
 * If {@link #terminate()} returns true, the query is terminated as if a
 * resource limit had been reached. For queries that return a {@link Result},
 * the result is unknown with explanation
 * {@link UnknownExplanation#INTERRUPTED}.
 * <p>
 * A termination request only applies to the query during which it was issued:
 * after {@link #terminate()} returned true, it is not called again during
 * that query, and the solver can be used for further queries afterwards.
 * Function {@link #terminate()} is called at the beginning of each query, i.e.,
 * if it keeps returning true, subsequent queries are terminated immediately.
 * <p>
 * If {@link #terminate()} throws an exception, the query is terminated and the
 * exception is rethrown by the method that executed the query.
 * <p>
 * Function {@link #terminate()} is called frequently from the thread that
 * executes the query, and must thus be cheap to evaluate. To terminate a query
 * from another thread, {@link #terminate()} can, e.g., check a flag of type
 * {@code java.util.concurrent.atomic.AtomicBoolean} that is set by that
 * thread.
 *
 * @api.note This interface is experimental and may change in future versions.
 */
@FunctionalInterface
public interface ITerminator {
  /**
   * Determine whether the current query of the solver this terminator is
   * connected to should be terminated.
   *
   * @return True to terminate the current query.
   */
  boolean terminate();
}
