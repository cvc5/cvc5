package cvc3;

import java.util.*;

/** mirrors CVC3::DebugException */
public class DebugException extends Cvc3Exception {

    private final static long serialVersionUID = 1L;

    public DebugException(String message) {
	super(message);
    }
}
