package cvc3;

import java.util.*;

public class Flag extends Embedded {
    // jni methods
    private static native boolean  jniIsNull(Object Flag) throws Cvc3Exception;
    private static native boolean  jniIsBool(Object Flag) throws Cvc3Exception;
    private static native boolean  jniIsInt(Object Flag) throws Cvc3Exception;
    private static native boolean  jniIsString(Object Flag) throws Cvc3Exception;
    private static native boolean  jniIsStringVec(Object Flag) throws Cvc3Exception;
    private static native boolean  jniGetBool(Object Flag) throws Cvc3Exception;
    private static native int      jniGetInt(Object Flag) throws Cvc3Exception;
    private static native String   jniGetString(Object Flag) throws Cvc3Exception;
    private static native String   jniGetHelp(Object Flag) throws Cvc3Exception;


    /// Constructor

    // create embedded object
    public Flag(Object Flag, EmbeddedManager embeddedManager) {
	super(Flag, embeddedManager);
    }


    /// API immutable
    
    boolean isNull() throws Cvc3Exception {
	return jniIsNull(embedded());
    }

    boolean isBool() throws Cvc3Exception {
	return jniIsBool(embedded());
    }

    boolean isInt() throws Cvc3Exception {
	return jniIsInt(embedded());
    }

    boolean isString() throws Cvc3Exception {
	return jniIsString(embedded());
    }

    boolean isStringVec() throws Cvc3Exception {
	return jniIsStringVec(embedded());
    }

    boolean getBool() throws Cvc3Exception {
	return jniGetBool(embedded());
    }

    int getInt() throws Cvc3Exception {
	return jniGetInt(embedded());
    }

    String getString() throws Cvc3Exception {
	return jniGetString(embedded());
    }

    String getHelp() throws Cvc3Exception {
	return jniGetHelp(embedded());
    }
}
