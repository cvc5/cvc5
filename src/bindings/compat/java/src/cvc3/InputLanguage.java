package cvc3;

import java.util.*;

/** See comments about mapping c++ enums to java in QueryResult */
public class InputLanguage {
    private final String d_lang;

    private InputLanguage(String lang) {
	d_lang = lang;
    }


    // names of c++ enum values
    public static final InputLanguage PRESENTATION = new InputLanguage("PRESENTATION");
    public static final InputLanguage SMTLIB = new InputLanguage("SMTLIB");
    public static final InputLanguage LISP = new InputLanguage("LISP");

    // the InputLanguage corresponding to a c++ enum value by name
    public static InputLanguage get(String value) throws DebugException {
	if (value.equals(PRESENTATION.toString())) {
	    return PRESENTATION;
	} else if (value.equals(SMTLIB.toString())) {
	    return SMTLIB;
	} else if (value.equals(LISP.toString())) {
	    return LISP;
	} else {
	    throw new DebugException("InputLanguage.constructor: unknown enum value: " + value);
	}
    }

    // the InputLanguage's c++ enum value
    public String toString() {
	return d_lang;
    }
}
