package cvc3;

import java.util.*;

/** A truth value of a formula. */
public class FormulaValue {
    private final String d_result;

    protected FormulaValue(String result) {
	d_result = result;
    }


    // names of c++ enum values
    public static final FormulaValue TRUE = new FormulaValue("TRUE_VAL");
    public static final FormulaValue FALSE = new FormulaValue("FALSE_VAL");
    public static final FormulaValue UNKNOWN = new FormulaValue("UNKNOWN_VAL");

    // the FormulaValue corresponding to a c++ enum value by name
    public static FormulaValue get(String value) throws DebugException {
	if (value.equals(TRUE.toString())) {
	    return TRUE;
	} else if (value.equals(FALSE.toString())) {
	    return FALSE;
	} else if (value.equals(UNKNOWN.toString())) {
	    return UNKNOWN;
	} else {
	    throw new DebugException("FormulaValue.constructor: unknown enum value: " + value);
	}
    }

    // the FormulaValue's c++ enum value
    public String toString() {
	return d_result;
    }
}
