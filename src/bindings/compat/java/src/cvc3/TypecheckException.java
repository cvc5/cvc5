package cvc3;

import java.util.*;

/** mirrors CVC3::TypecheckException */
public class TypecheckException extends Cvc3Exception {

    private final static long serialVersionUID = 1L;

    public TypecheckException(String message) {
	super(message);
    }
}
