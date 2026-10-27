/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Black box testing of the Pair class of the Java API.
 */

package tests;

import static org.junit.jupiter.api.Assertions.*;

import io.github.cvc5.Pair;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;
import org.junit.jupiter.api.Test;

class PairTest
{
  @Test
  void equalHash()
  {
    Pair<String, Integer> p1 = new Pair<>("x", 1);
    Pair<String, Integer> p2 = new Pair<>("x", 1);
    Pair<String, Integer> p3 = new Pair<>("y", 1);
    Pair<String, Integer> p4 = new Pair<>("x", 2);

    assertEquals(p1, p1);
    assertEquals(p1, p2);
    assertNotEquals(p1, p3);
    assertNotEquals(p1, p4);

    assertEquals(p1.hashCode(), p1.hashCode());
    assertEquals(p1.hashCode(), p2.hashCode());
  }

  @Test
  void nullElements()
  {
    Pair<String, Integer> p1 = new Pair<>(null, 1);
    Pair<String, Integer> p2 = new Pair<>(null, 1);
    Pair<String, Integer> p3 = new Pair<>("x", null);

    assertEquals(p1, p2);
    assertEquals(p1.hashCode(), p2.hashCode());
    assertNotEquals(p1, p3);
    assertNotEquals(p1, new Pair<>("x", 1));
    assertNotEquals(new Pair<>("x", 1), p1);

    Set<Pair<String, Integer>> set = new HashSet<>();
    set.add(new Pair<>(null, 1));
    assertTrue(set.contains(new Pair<>(null, 1)));
  }

  @Test
  void hashBasedCollections()
  {
    Set<Pair<String, Integer>> set = new HashSet<>();
    set.add(new Pair<>("x", 1));
    set.add(new Pair<>("x", 1));
    assertEquals(1, set.size());
    assertTrue(set.contains(new Pair<>("x", 1)));
    assertFalse(set.contains(new Pair<>("x", 2)));

    Map<Pair<String, Integer>, String> map = new HashMap<>();
    map.put(new Pair<>("x", 1), "value");
    assertEquals("value", map.get(new Pair<>("x", 1)));
  }
}
