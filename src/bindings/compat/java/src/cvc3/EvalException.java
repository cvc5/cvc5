package cvc3;

import java.util.*;

/** mirrors CVC3::EvalException */
public class EvalException extends Cvc3Exception {

    private final static long serialVersionUID = 1L;

    public EvalException(String message) {
	super(message);
    }
}
