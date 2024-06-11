/******************************************************************************
 * Top contributors (to current version):
 *   Hans-Jörg Schurr, Mudathir Mohamed, Andres Noetzli
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2024 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * The cvc5 java API.
 */

package io.github.cvc5;

import java.math.BigInteger;

/**
 * A cvc5 Proof.
 */
public class Proof implements IPointer
{
  /**
   * Null proof
   */
  public Proof()
  {
    this(getNullProof());
  }

  private static native long getNullProof();

  Proof(long pointer)
  {
    this.pointer = pointer;
  }

  protected long pointer;

  public void deletePointer()
  {
    if (pointer != 0)
    {
      deletePointer(pointer);
    }
    pointer = 0;
  }

  protected native void deletePointer(long pointer);

  public long getPointer()
  {
    return pointer;
  }

  /**
   * @return The proof rule used by the root step of the proof.
   * @throws CVC5ApiException
   */
  public ProofRule getRule() throws CVC5ApiException
  {
    int value = getRule(pointer);
    return ProofRule.fromInt(value);
  }

  private native int getRule(long pointer);

  /**
   * @return The proof rewrite rule used by the root step of the proof.
   * @throws CVC5ApiException if `getRule()` does not return `DSL_REWRITE`
   *         or `THEORY_REWRITE`.
   */
  public ProofRewriteRule getRewriteRule() throws CVC5ApiException
  {
    int value = getRewriteRule(pointer);
    return ProofRewriteRule.fromInt(value);
  }

  private native int getRewriteRule(long pointer);

  /** @return The conclusion of the root step of the proof. */
  public Term getResult()
  {
    long termPointer = getResult(pointer);
    return new Term(termPointer);
  }

  private native long getResult(long pointer);

  /** @return The premises of the root step of the proof. */
  public Proof[] getChildren()
  {
    long[] proofPointers = getChildren(pointer);
    return Utils.getProofs(proofPointers);
  }

  private native long[] getChildren(long pointer);

  /**
   * @return The arguments of the root step of the proof as a vector of terms.
   *         Some of those terms might be strings.
   */
  public Term[] getArguments()
  {
    long[] termPointers = getArguments(pointer);
    return Utils.getTerms(termPointers);
  }

  private native long[] getArguments(long pointer);

  /**
   * Referential equality operator.
   * Return `true` if both proofs point to the same internal proof object.
   *
   * @param p The proof to compare to for equality.
   * @return `true` if the proofs are equal.
   */
  @Override
  public boolean equals(Object p)
  {
    if (this == p)
    {
      return true;
    }
    if (p == null || getClass() != p.getClass())
    {
      return false;
    }
    Proof proof = (Proof) p;
    if (pointer == proof.pointer)
    {
      return true;
    }
    return equals(pointer, proof.getPointer());
  }

  private native boolean equals(long pointer1, long pointer2);

  /** @return The hash value of the proof. */
  @Override
  public int hashCode()
  {
    return hashCode(pointer);
  }

  private native int hashCode(long pointer);
}
