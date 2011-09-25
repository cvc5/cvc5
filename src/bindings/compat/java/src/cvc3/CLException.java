package cvc3;

import java.util.*;

/** mirrors CVC3::CLException */
class CLException extends Cvc3Exception {

    private final static long serialVersionUID = 1L;

    public CLException(String message) {
	super(message);
    }
}
