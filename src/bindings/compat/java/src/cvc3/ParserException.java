package cvc3;

import java.util.*;

/** mirrors CVC3::ParserException */
public class ParserException extends Cvc3Exception {

    private final static long serialVersionUID = 1L;

    public ParserException(String message) {
	super(message);
    }
}
