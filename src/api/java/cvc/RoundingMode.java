package cvc;

public enum RoundingMode
{
  ROUND_NEAREST_TIES_TO_EVEN(0),
  ROUND_TOWARD_POSITIVE(1),
  ROUND_TOWARD_NEGATIVE(2),
  ROUND_TOWARD_ZERO(3),
  ROUND_NEAREST_TIES_TO_AWAY(4);

  private int value;

  private RoundingMode(int value)
  {
    this.value = value;
  }

  public int getValue()
  {
    return value;
  }
}
