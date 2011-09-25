package cvc3;

import java.util.*;

public class Op extends Embedded {
    // jni methods
    private static native boolean
	jniEquals(Object Expr1, Object Expr2) throws Cvc3Exception;
    private static native String
	jniToString(Object Expr) throws Cvc3Exception;

    private static native Object
	jniGetExpr(Object op) throws Cvc3Exception;
    private static native boolean
	jniIsNull(Object Op) throws Cvc3Exception;

    /// Constructor

    public Op(Object Op, EmbeddedManager embeddedManager) {
	super(Op, embeddedManager);
    }


    /// API (immutable)

    public boolean equals(Object o) {
	if (this == o) return true;

	if (!(o instanceof Op)) return false;
	boolean result = false;
	try {
	    result = jniEquals(embedded(), ((Embedded)o).embedded());
	} catch (Cvc3Exception e) {
	    assert(false);
	}
	return result;
    } 
 
    // must return the same hash code for two objects if equals returns true
    public int hashCode() {
	try {
	    return getExpr().hashCode();
	} catch (Cvc3Exception e) {
	    assert(false);
	}
	return 0;
    }
    
    public String toString() {
	String result = "";
	try {
	    result = jniToString(embedded());
	} catch (Cvc3Exception e) {
	    assert(false);
	}
	return result;
    }
 
    public ExprMut getExpr() throws Cvc3Exception {
	return new ExprMut(jniGetExpr(embedded()), embeddedManager());
    }

    public boolean isNull() throws Cvc3Exception {
	return jniIsNull(embedded());
    }
}
