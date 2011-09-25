package cvc3;

import java.util.*;

public abstract class Flags extends Embedded {
    // jni methods
    private static native Object[] jniGetFlags(Object Flags, String prefix) throws Cvc3Exception;
    private static native Object jniGetFlag(Object Flags, String name) throws Cvc3Exception;


    /// Constructor

    // create embedded object
    public Flags(Object Flags, EmbeddedManager embeddedManager) {
	super(Flags, embeddedManager);
    }

    /// API (immutable)


    // get names of all flags starting with prefix
    public List getFlags(String prefix) throws Cvc3Exception {
	Object[] flags = jniGetFlags(embedded(), prefix);
	assert(flags instanceof String[]);
	return Arrays.asList(flags);
    }

    // get the value of a flag by name (without prefix -/+)
    public Flag getFlag(String name) throws Cvc3Exception {
	return new Flag(jniGetFlag(embedded(), name), embeddedManager());
    }
}
