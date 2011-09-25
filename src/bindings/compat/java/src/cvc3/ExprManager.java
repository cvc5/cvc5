package cvc3;

import java.util.*;

public class ExprManager extends Embedded {
    // jni methods
    private static native String jniGetInputLanguage(Object ExprManager) throws Cvc3Exception;
    private static native String jniGetOutputLanguage(Object ExprManager) throws Cvc3Exception;

    /// Constructor

    public ExprManager(Object ExprManager, EmbeddedManager embeddedManager) {
	super(ExprManager, embeddedManager);
    }


    /// API (immutable)

    public InputLanguage getInputLanguage() throws Cvc3Exception {
	return InputLanguage.get(jniGetInputLanguage(embedded()));
    }

    public InputLanguage getOutputLanguage() throws Cvc3Exception {
	return InputLanguage.get(jniGetOutputLanguage(embedded()));
    }
}
