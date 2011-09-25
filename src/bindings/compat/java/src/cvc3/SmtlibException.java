package cvc3;

import java.util.*;

/** mirrors CVC3::SmtlibException */
public class SmtlibException extends Cvc3Exception {

    private final static long serialVersionUID = 1L;

    public SmtlibException(String message) {
	super(message);
    }
}
