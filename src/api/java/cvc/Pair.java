package cvc;

public class Pair<K, V>
{
  public K first;
  public V second;
  public Pair(K first, V second)
  {
    this.first = first;
    this.second = second;
  }

  @Override public boolean equals(Object pair)
  {
    if (this == pair)
      return true;
    if (pair == null || getClass() != pair.getClass())
      return false;

    Pair<K, V> p = (Pair<K, V>) pair;

    if (!first.equals(p.first))
      return false;
    return second.equals(p.second);
  }
}
