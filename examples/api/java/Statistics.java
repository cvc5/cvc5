/******************************************************************************
 * Top contributors (to current version):
 *   Mudathir Mohamed, Gereon Kremer, Andres Noetzli
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2025 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * An example of accessing cvc5's statistics using the Java API.
 */

import static io.github.cvc5.Kind.*;

import io.github.cvc5.*;
import java.util.List;
import java.util.Map;

public class Statistics
{
  public static void main(String[] args)
  {
    TermManager tm = new TermManager();
    Solver solver = new Solver(tm);
    {
      // Get the statistics from the `Solver` and iterate over them. The
      // `Statistics` class implements the `Iterable<Pair<String, Stat>>` interface.
      io.github.cvc5.Statistics stats = solver.getStatistics();
      // short version
      System.out.println("Short version:");
      System.out.println(stats);

      System.out.println("-------------------------------------------------------");

      System.out.println("Long version:");

      // long version
      for (Map.Entry<String, Stat> pair : stats)
      {
        Stat stat = pair.getValue();
        if (stat.isInt())
        {
          System.out.println(pair.getKey() + " = " + stat.getInt());
        }
        else if (stat.isDouble())
        {
          System.out.println(pair.getKey() + " = " + stat.getDouble());
        }
        else if (stat.isString())
        {
          System.out.println(pair.getKey() + " = " + stat.getString());
        }
        else if (stat.isHistogram())
        {
          System.out.println("-------------------------------------------------------");
          System.out.println(pair.getKey() + " : Map");
          for (Map.Entry<String, Long> entry : stat.getHistogram().entrySet())
          {
            System.out.println(entry.getKey() + " = " + entry.getValue());
          }
          System.out.println("-------------------------------------------------------");
        }
      }
    }
    Context.deletePointers();
  } 
}
