/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Black box testing of the Triplet class of the Java API.
 */

package tests;

import static org.junit.jupiter.api.Assertions.*;

import io.github.cvc5.Triplet;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;
import org.junit.jupiter.api.Test;

class TripletTest
{
  @Test
  void equalHash()
  {
    Triplet<String, Integer, Boolean> t1 = new Triplet<>("x", 1, true);
    Triplet<String, Integer, Boolean> t2 = new Triplet<>("x", 1, true);
    Triplet<String, Integer, Boolean> t3 = new Triplet<>("y", 1, true);
    Triplet<String, Integer, Boolean> t4 = new Triplet<>("x", 2, true);
    Triplet<String, Integer, Boolean> t5 = new Triplet<>("x", 1, false);

    assertEquals(t1, t1);
    assertEquals(t1, t2);
    assertNotEquals(t1, t3);
    assertNotEquals(t1, t4);
    assertNotEquals(t1, t5);

    assertEquals(t1.hashCode(), t1.hashCode());
    assertEquals(t1.hashCode(), t2.hashCode());
  }

  @Test
  void nullElements()
  {
    Triplet<String, Integer, Boolean> t1 = new Triplet<>(null, 1, true);
    Triplet<String, Integer, Boolean> t2 = new Triplet<>(null, 1, true);
    Triplet<String, Integer, Boolean> t3 = new Triplet<>("x", 1, null);

    assertEquals(t1, t2);
    assertEquals(t1.hashCode(), t2.hashCode());
    assertNotEquals(t1, t3);
    assertNotEquals(t1, new Triplet<>("x", 1, true));
    assertNotEquals(new Triplet<>("x", 1, true), t1);

    Set<Triplet<String, Integer, Boolean>> set = new HashSet<>();
    set.add(new Triplet<>(null, 1, true));
    assertTrue(set.contains(new Triplet<>(null, 1, true)));
  }

  @Test
  void hashBasedCollections()
  {
    Set<Triplet<String, Integer, Boolean>> set = new HashSet<>();
    set.add(new Triplet<>("x", 1, true));
    set.add(new Triplet<>("x", 1, true));
    assertEquals(1, set.size());
    assertTrue(set.contains(new Triplet<>("x", 1, true)));
    assertFalse(set.contains(new Triplet<>("x", 1, false)));

    Map<Triplet<String, Integer, Boolean>, String> map = new HashMap<>();
    map.put(new Triplet<>("x", 1, true), "value");
    assertEquals("value", map.get(new Triplet<>("x", 1, true)));
  }
}
