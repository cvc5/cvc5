/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Black box testing of the native memory management of the Java API.
 *
 * Native objects are freed once their Java wrappers are unreachable: objects
 * of a term manager that is still in use are freed on the next use of that
 * term manager, and everything else once the term manager and all objects
 * derived from it are unreachable. Explicit release is immediate.
 */

package tests;

import static io.github.cvc5.Kind.*;
import static org.junit.jupiter.api.Assertions.*;

import io.github.cvc5.*;
import java.lang.ref.Reference;
import java.lang.ref.WeakReference;
import java.lang.reflect.Method;
import java.util.ArrayList;
import java.util.List;
import java.util.concurrent.ExecutorService;
import java.util.concurrent.Executors;
import java.util.concurrent.Future;
import java.util.concurrent.TimeUnit;
import java.util.concurrent.atomic.AtomicInteger;
import java.util.function.BooleanSupplier;
import org.junit.jupiter.api.Test;

class MemoryManagementTest
{
  /* Hooks into io.github.cvc5.NativeContext, which is package-private. */

  /** The number of native objects freed so far in the context of the given object. */
  private static long freedObjects(Object object) throws Exception
  {
    Class<?> nativeContext = Class.forName("io.github.cvc5.NativeContext");
    Class<?> abstractPointer = Class.forName("io.github.cvc5.AbstractPointer");
    Method m = nativeContext.getDeclaredMethod("freedObjects", abstractPointer);
    m.setAccessible(true);
    return (Long) m.invoke(null, object);
  }

  /** The number of term manager contexts reclaimed after becoming unreachable. */
  private static long releasedContexts() throws Exception
  {
    Class<?> nativeContext = Class.forName("io.github.cvc5.NativeContext");
    Method m = nativeContext.getDeclaredMethod("releasedContexts");
    m.setAccessible(true);
    return (Long) m.invoke(null);
  }

  /** Run the garbage collector until the condition holds or a timeout expires. */
  private static boolean eventually(BooleanSupplier condition) throws InterruptedException
  {
    for (int i = 0; i < 200; i++)
    {
      if (condition.getAsBoolean())
      {
        return true;
      }
      System.gc();
      Thread.sleep(25);
    }
    return condition.getAsBoolean();
  }

  private static class CountingPlugin extends AbstractPlugin
  {
    final AtomicInteger checks = new AtomicInteger();

    CountingPlugin(TermManager tm)
    {
      super(tm);
    }

    @Override
    public Term[] check()
    {
      checks.incrementAndGet();
      return new Term[0];
    }

    @Override
    public String getName()
    {
      return "CountingPlugin";
    }
  }

  /* Helpers that create objects and drop every strong reference to them on return. */

  private static WeakReference<Term> temporaryTerm(TermManager tm, int i)
  {
    return new WeakReference<>(tm.mkInteger(i));
  }

  private static WeakReference<CountingPlugin> addTemporaryPlugin(Solver solver)
  {
    CountingPlugin plugin = new CountingPlugin(solver.getTermManager());
    solver.addPlugin(plugin);
    return new WeakReference<>(plugin);
  }

  private static WeakReference<Solver> temporarySolverWithPlugin(TermManager tm)
  {
    Solver solver = new Solver(tm);
    solver.addPlugin(new CountingPlugin(tm));
    return new WeakReference<>(solver);
  }

  private static void useAndDropEverything() throws CVC5ApiException
  {
    TermManager tm = new TermManager();
    Solver solver = new Solver(tm);
    solver.setOption("oracles", "true");
    solver.addPlugin(new CountingPlugin(tm));
    SymbolManager sm = new SymbolManager(tm);
    InputParser parser = new InputParser(solver, sm);
    parser.setIncrementalStringInput(io.github.cvc5.modes.InputLanguage.SMT_LIB_2_6, "test");
    parser.appendIncrementalStringInput("(set-logic ALL)(declare-fun y () Int)");
    parser.nextCommand().invoke(solver, sm);
    parser.nextCommand().invoke(solver, sm);
    Sort intSort = tm.getIntegerSort();
    Term f = solver.declareOracleFun("f", new Sort[] {intSort}, intSort, args -> tm.mkInteger(1));
    Term x = tm.mkConst(intSort, "x");
    solver.assertFormula(tm.mkTerm(EQUAL, tm.mkTerm(APPLY_UF, f, x), tm.mkInteger(1)));
    assertTrue(solver.checkSat().isSat());
  }

  @Test
  void unreachableObjectsAreFreedOnNextUse() throws Exception
  {
    TermManager tm = new TermManager();
    List<WeakReference<Term>> refs = new ArrayList<>();
    for (int i = 0; i < 1000; i++)
    {
      refs.add(temporaryTerm(tm, i));
    }
    long freedBefore = freedObjects(tm);
    assertTrue(eventually(() -> refs.stream().allMatch(r -> r.get() == null)));
    // The wrappers are gone; the native terms are freed on the next use of tm.
    assertEquals(freedBefore, freedObjects(tm));
    Term t = tm.mkTrue();
    assertTrue(freedObjects(tm) >= freedBefore + 1000);
    assertTrue(t.isBooleanValue());
  }

  @Test
  void explicitReleaseIsImmediateAndIdempotent() throws Exception
  {
    TermManager tm = new TermManager();
    Solver solver = new Solver(tm);
    Term t = tm.mkTrue();
    long freedBefore = freedObjects(tm);
    solver.deletePointer();
    assertEquals(freedBefore + 1, freedObjects(tm));
    assertEquals(0, solver.getPointer());
    solver.deletePointer();
    solver.close();
    assertEquals(freedBefore + 1, freedObjects(tm));
    // Objects derived from a term manager survive its release.
    tm.close();
    assertEquals(freedBefore + 2, freedObjects(tm));
    assertEquals(0, tm.getPointer());
    assertTrue(t.isBooleanValue());
    t.deletePointer();
    assertEquals(freedBefore + 3, freedObjects(tm));
  }

  @Test
  void solverKeepsItsCallbacksAlive() throws Exception
  {
    TermManager tm = new TermManager();
    Solver solver = new Solver(tm);
    WeakReference<CountingPlugin> plugin = addTemporaryPlugin(solver);
    // Native code references the plugin only weakly; the solver keeps it alive.
    for (int i = 0; i < 5; i++)
    {
      System.gc();
      Thread.sleep(10);
    }
    assertNotNull(plugin.get());
    solver.assertFormula(tm.mkConst(tm.getBooleanSort(), "b"));
    assertTrue(solver.checkSat().isSat());
    assertTrue(plugin.get().checks.get() > 0);
    Reference.reachabilityFence(solver);
  }

  @Test
  void unreachableSolverReleasesItsCallbacks() throws Exception
  {
    TermManager tm = new TermManager();
    WeakReference<Solver> solver = temporarySolverWithPlugin(tm);
    assertTrue(eventually(() -> solver.get() == null));
    long freedBefore = freedObjects(tm);
    // Deferred until the next use of the term manager.
    Term t = tm.mkTrue();
    assertTrue(freedObjects(tm) > freedBefore);
    assertTrue(t.isBooleanValue());
  }

  @Test
  void unreachableTermManagerIsReclaimed() throws Exception
  {
    long releasedBefore = releasedContexts();
    useAndDropEverything();
    assertTrue(eventually(() -> {
      try
      {
        return releasedContexts() > releasedBefore;
      }
      catch (Exception e)
      {
        throw new RuntimeException(e);
      }
    }));
  }

  @Test
  void accessorsReturnTheSameInstances() throws Exception
  {
    TermManager tm = new TermManager();
    Solver solver = new Solver(tm);
    assertSame(solver.getTermManager(), solver.getTermManager());
    SymbolManager sm = new SymbolManager(tm);
    InputParser parser = new InputParser(solver, sm);
    assertSame(solver, parser.getSolver());
    assertSame(sm, parser.getSymbolManager());
    InputParser parser2 = new InputParser(solver);
    assertSame(solver, parser2.getSolver());
    assertSame(parser2.getSymbolManager(), parser2.getSymbolManager());
  }

  @Test
  @SuppressWarnings("deprecation")
  void contextDeletePointersFreesEverything() throws Exception
  {
    TermManager tm = new TermManager();
    Solver solver = new Solver(tm);
    Term t = tm.mkTrue();
    long freedBefore = freedObjects(tm);
    Context.deletePointers();
    assertEquals(freedBefore + 3, freedObjects(tm));
    assertEquals(0, tm.getPointer());
    assertEquals(0, solver.getPointer());
    assertEquals(0, t.getPointer());
    // Idempotent, and new objects can still be created.
    Context.deletePointers();
    assertEquals(freedBefore + 3, freedObjects(tm));
    TermManager tm2 = new TermManager();
    assertTrue(tm2.mkTrue().isBooleanValue());
  }

  @Test
  void objectsCanBeHandedOverBetweenThreads() throws Exception
  {
    List<Object> handover = new ArrayList<>();
    Thread producer = new Thread(() -> {
      TermManager tm = new TermManager();
      Solver solver = new Solver(tm);
      solver.addPlugin(new CountingPlugin(tm));
      Term x = tm.mkConst(tm.getIntegerSort(), "x");
      handover.add(tm);
      handover.add(solver);
      handover.add(tm.mkTerm(GT, x, tm.mkInteger(0)));
    });
    producer.start();
    producer.join(); // synchronizes the hand-over
    TermManager tm = (TermManager) handover.get(0);
    Solver solver = (Solver) handover.get(1);
    Term t = (Term) handover.get(2);
    assertEquals(GT, t.getKind());
    solver.assertFormula(t);
    // Plugin callbacks run on this thread, not the one that registered the plugin.
    Result r = solver.checkSat();
    assertTrue(r.isSat(), r.toString());
    tm.close();
    Sort s = t.getSort();
    assertTrue(s.isBoolean(), s.toString());
  }

  @Test
  void separateTermManagersInSeparateThreads() throws Exception
  {
    int numThreads = 8;
    ExecutorService pool = Executors.newFixedThreadPool(numThreads);
    List<Future<Integer>> results = new ArrayList<>();
    for (int i = 0; i < numThreads; i++)
    {
      final int seed = i;
      results.add(pool.submit(() -> {
        int sat = 0;
        for (int round = 0; round < 20; round++)
        {
          // Half of the rounds release explicitly, the other half rely on
          // garbage collection.
          if (round % 2 == 0)
          {
            try (TermManager tm = new TermManager(); Solver solver = new Solver(tm))
            {
              sat += solve(tm, solver, seed + round);
            }
          }
          else
          {
            TermManager tm = new TermManager();
            sat += solve(tm, new Solver(tm), seed + round);
          }
          if (round % 5 == 0)
          {
            System.gc();
          }
        }
        return sat;
      }));
    }
    pool.shutdown();
    assertTrue(pool.awaitTermination(5, TimeUnit.MINUTES));
    for (Future<Integer> result : results)
    {
      assertEquals(20, result.get());
    }
  }

  private static int solve(TermManager tm, Solver solver, int n) throws CVC5ApiException
  {
    solver.setOption("produce-models", "true");
    Sort intSort = tm.getIntegerSort();
    Term x = tm.mkConst(intSort, "x");
    Term sum = tm.mkInteger(0);
    for (int i = 0; i < 200; i++)
    {
      sum = tm.mkTerm(ADD, sum, tm.mkTerm(MULT, tm.mkInteger(i), x));
    }
    solver.assertFormula(tm.mkTerm(GT, sum, tm.mkInteger(n)));
    Result r = solver.checkSat();
    assertTrue(solver.getValue(x).isIntegerValue());
    return r.isSat() ? 1 : 0;
  }
}
