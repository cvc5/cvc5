package cvc3;

import java.util.*;

public class Rational extends Embedded {
    // jni methods
    private static native Object
	jniRational1(int n, int d) throws Cvc3Exception;
    private static native Object
	jniRational2(String n, int base) throws Cvc3Exception;
    private static native Object
	jniRational3(String n, String d, int base) throws Cvc3Exception;
    
    private static native boolean
	jniEquals(Object Rational1, Object Rational2) throws Cvc3Exception;
    private static native String
	jniToString(Object Rational) throws Cvc3Exception;
    private static native int
	jniHash(Object Rational) throws Cvc3Exception;

    private static native boolean
	jniIsLe(Object Rational1, Object Rational2) throws Cvc3Exception;
    private static native boolean
	jniIsLt(Object Rational1, Object Rational2) throws Cvc3Exception;
    private static native boolean
	jniIsGe(Object Rational1, Object Rational2) throws Cvc3Exception;
    private static native boolean
	jniIsGt(Object Rational1, Object Rational2) throws Cvc3Exception;

    private static native Object
	jniPlus(Object Rational1, Object Rational2) throws Cvc3Exception;
    private static native Object
	jniMinus(Object Rational1, Object Rational2) throws Cvc3Exception;
    private static native Object
	jniMult(Object Rational1, Object Rational2) throws Cvc3Exception;
    private static native Object
	jniDivide(Object Rational1, Object Rational2) throws Cvc3Exception;
    private static native Object
	jniMod(Object Rational1, Object Rational2) throws Cvc3Exception;


    private static native Object
	jniGetNumerator(Object Rational) throws Cvc3Exception;
    private static native Object
	jniGetDenominator(Object Rational) throws Cvc3Exception;
    private static native boolean
	jniIsInteger(Object Rational) throws Cvc3Exception;
    private static native int
	jniGetInteger(Object Rational) throws Cvc3Exception;


    private static native Object
	jniGcd(Object Rational1, Object Rational2) throws Cvc3Exception;
    private static native Object
	jniLcm(Object Rational1, Object Rational2) throws Cvc3Exception;
    private static native Object
	jniAbs(Object Rational) throws Cvc3Exception;
    private static native Object
	jniFloor(Object Rational) throws Cvc3Exception;
    private static native Object
	jniCeil(Object Rational) throws Cvc3Exception;

    /// Constructor

    public Rational(Object Rational, EmbeddedManager embeddedManager) {
	super(Rational, embeddedManager);
    }


    public Rational(int n, EmbeddedManager embeddedManager) throws Cvc3Exception {
	this(jniRational1(n, 10), embeddedManager);
    }

    public Rational(int n, int d, EmbeddedManager embeddedManager) throws Cvc3Exception {
	this(jniRational1(n, d), embeddedManager);
    }

    public Rational(String n, EmbeddedManager embeddedManager) throws Cvc3Exception {
	this(jniRational2(n, 10), embeddedManager);
    }

    public Rational(String n, int base, EmbeddedManager embeddedManager) throws Cvc3Exception {
	this(jniRational2(n, base), embeddedManager);
    }

    public Rational(String n, String d, EmbeddedManager embeddedManager) throws Cvc3Exception {
	this(jniRational3(n, d, 10), embeddedManager);
    }

    public Rational(String n, String d, int base, EmbeddedManager embeddedManager) throws Cvc3Exception {
	this(jniRational3(n, d, base), embeddedManager);
    }



    /// API (immutable)

    // 'Problem' with equals/hashCode:
    // this is based on the wrapped c++ expressions.
    // as a consequence two Expr objects are equal iff
    // the wrapped expression is equal,
    // and are indistinguishable for example in a HashMap.

    public boolean equals(Object o) {
	if (this == o) return true;

	if (!(o instanceof Rational)) return false;
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
	    return jniHash(embedded());
	} catch (Cvc3Exception e) {
	    assert(false);
	}
	assert(false);
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


    public boolean isLt(Rational r) throws Cvc3Exception {
	return jniIsLt(embedded(), r.embedded());
    }

    public boolean isLe(Rational r) throws Cvc3Exception {
	return jniIsLe(embedded(), r.embedded());
    }

    public boolean isGt(Rational r) throws Cvc3Exception {
	return jniIsGt(embedded(), r.embedded());
    }

    public boolean isGe(Rational r) throws Cvc3Exception {
	return jniIsGe(embedded(), r.embedded());
    }



    public Rational plus(Rational r) throws Cvc3Exception {
	return new Rational(jniPlus(embedded(), r.embedded()), embeddedManager());
    }

    public Rational minus(Rational r) throws Cvc3Exception {
	return new Rational(jniPlus(embedded(), r.embedded()), embeddedManager());
    }

    public Rational mult(Rational r) throws Cvc3Exception {
	return new Rational(jniPlus(embedded(), r.embedded()), embeddedManager());
    }

    public Rational divide(Rational r) throws Cvc3Exception {
	return new Rational(jniPlus(embedded(), r.embedded()), embeddedManager());
    }

    public Rational mod(Rational r) throws Cvc3Exception {
	return new Rational(jniPlus(embedded(), r.embedded()), embeddedManager());
    }



    public Rational getNumerator() throws Cvc3Exception {
	return new Rational(jniGetNumerator(embedded()), embeddedManager());
    }

    public Rational getDenominator() throws Cvc3Exception {
	return new Rational(jniGetDenominator(embedded()), embeddedManager());
    }

    public boolean isInteger() throws Cvc3Exception {
	return jniIsInteger(embedded());
    }

    public int getInteger() throws Cvc3Exception {
        assert(isInteger());
        return jniGetInteger(embedded());
    }



    public Rational gcd(Rational r) throws Cvc3Exception {
	return new Rational(jniGcd(embedded(), r.embedded()), embeddedManager());
    }

    public Rational lcm(Rational r) throws Cvc3Exception {
	return new Rational(jniLcm(embedded(), r.embedded()), embeddedManager());
    }

    public Rational abs() throws Cvc3Exception {
	return new Rational(jniAbs(embedded()), embeddedManager());
    }

    public Rational floor() throws Cvc3Exception {
	return new Rational(jniFloor(embedded()), embeddedManager());
    }

    public Rational ceil() throws Cvc3Exception {
	return new Rational(jniCeil(embedded()), embeddedManager());
    }
}
