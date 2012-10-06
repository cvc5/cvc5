package cvc3;

import java.util.*;
import java.io.*;

/** Wrapper for a c++ object as a java Object.

    see README for details on garbage collection,
    i.e. interplay of delete, finalize, and EmbeddedManager to destruct
    the embedded c++ object. */
public abstract class Embedded {

    // load jni c++ library
    static {
        System.loadLibrary("cvc4");
        System.loadLibrary("cvc4parser");
        System.loadLibrary("cvc4compatjni");

	/*
	// for debugging: stop here by waiting for a key press,
	// and attach c++ debugger
	System.out.println("Loadded cvc3jni");
	
	try {
	    BufferedReader br = new BufferedReader(new InputStreamReader(System.in));
	    br.readLine();
	} catch (IOException ioe) {
	}
	*/
    }


    /// Attributes


    // embedded object
    protected Object d_embedded;

    // embedded object manager
    private final EmbeddedManager d_embeddedManager;


    /// Constructor


    // initialize with embedded object and EmbeddedManager
    // if EmbeddedManager is null then delete must be called before
    // Embedded is garbage collected
    protected Embedded(Object Embedded, EmbeddedManager embeddedManager) {
	//System.out.println("Create: Embedded");
	assert(Embedded != null);
	d_embedded = Embedded;
	d_embeddedManager = embeddedManager;
    }

    // access to embedded c++ object
    public synchronized Object embedded() {
	return d_embedded;
    }

    // access to EmbeddedManager (might be null if none used)
    public EmbeddedManager embeddedManager() {
	return d_embeddedManager;
    }

    // check if already destructed
    // (or queued for destruction in embeddedManager)
    public synchronized boolean isDeleted() {
	return (d_embedded == null);
    }

    // delete embedded object or enqueue it for deletion
    public synchronized void delete() throws Cvc3Exception {
	if (isDeleted()) return;

	// no embedded manager, so should be in main thread:
	// destruct right away
	if (d_embeddedManager == null) {
	    EmbeddedManager.jniDelete(d_embedded);
	}
	// could be in finalizer, so queue in embeddedManager;
	// unless the embeddedManager is already deleted,
	// then its (and this') ValidityChecker has been delete.
	// assuming this is an Expr or a Theorem it's embedded object
	// has then already been deleted as well.
	else {
	    synchronized(d_embeddedManager) {
		if (!d_embeddedManager.isDeleted()) {
		    d_embeddedManager.register(this);
		}
	    }
	}
	d_embedded = null;
    }

    // ensure that delete is called if finalization occurs
    public void finalize() throws Throwable {
	try {
	    // no embeddedManager, so deleted should have been called
	    if (d_embeddedManager == null) {
		if (d_embedded != null) {
		    assert(false);
//		    System.out.println("Embedded.Finalizer: should never be called");
		    throw new Error("Embedded.Finalizer: should never be called");
		}
	    }
	    else if (!d_embeddedManager.isDeleted()) {
		delete();
	    }
	} finally {
	    super.finalize();
	}
    }
}
