package cvc3;

import java.util.*;

public class FlagsMut extends Flags {
    // jni methods
    private static native void jniSetFlag1(Object Flags, String name, boolean value) throws Cvc3Exception;
    private static native void jniSetFlag2(Object Flags, String name, int value) throws Cvc3Exception;
    private static native void jniSetFlag3(Object Flags, String name, String value) throws Cvc3Exception;
    private static native void jniSetFlag4(Object Flags, String map, String name, boolean value) throws Cvc3Exception;
    
    
    /// Constructor

    // create embedded object
    public FlagsMut(Object FlagsMut, EmbeddedManager embeddedManager) {
	super(FlagsMut, embeddedManager);
    }

    
    /// API (mutable)

    public void setFlag(String name, boolean value) throws Cvc3Exception {
        jniSetFlag1(embedded(), name, value);
    }

    public void setFlag(String name, int value) throws Cvc3Exception {
        jniSetFlag2(embedded(), name, value);
    }

    public void setFlag(String name, String value) throws Cvc3Exception {
        jniSetFlag3(embedded(), name, value);
    }

    // flag representing set of options, e.g. trace
    public void setFlag(String map, String name, boolean value) throws Cvc3Exception {
        jniSetFlag4(embedded(), map, name, value);
    }
}
