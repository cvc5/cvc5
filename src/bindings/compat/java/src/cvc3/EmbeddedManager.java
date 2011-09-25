package cvc3;

import java.util.*;

/** Helps to enforce deallocation of a set of embedded objects

    See also Embedded.java

    Cvc3 requires on the C++ level that the ValidityChecker is destructed
    last, after all other Cvc3 objects (i.e. subclasses of Embedded).

    A 'simple' (but not too cheap) way to achieve this effect of deterministic
    deallocation in Java without introducing much error prone code is to
    register all embedded objects (except for the ValidityChecker)
    with an EmbeddedManager.

    When the ValidityChecker is deleted/finalized it uses the EmbeddedManager
    to destruct all other Cvc3 objects first.
*/
public class EmbeddedManager {
    // jni methods

    // call the destructor of the c++ object
    public static native void jniDelete(Object Embedded) throws Cvc3Exception;


    // c++ objects which have been registered for deletion
    private List d_deleted;


    /// Constructor

    // delete must be called before EmbeddedManager is garbage collected
    public EmbeddedManager() {
	d_deleted = new ArrayList();
    }


    /// Methods

    // true iff delete has been called
    public synchronized boolean isDeleted() {
	return (d_deleted == null);
    }

    // signals that the ValidityChecker destructs itself
    public synchronized void delete() throws Cvc3Exception {
	d_deleted = null;
    }

    // registers a c++ object for deletion
    public synchronized void register(Embedded embedded) {
	d_deleted.add(embedded.embedded());
    }

    // destruct all registered objects
    public synchronized void cleanUp() throws Cvc3Exception {
	assert(!isDeleted());
	Iterator i = d_deleted.iterator();
	while (i.hasNext()) {
	    jniDelete(i.next());
	}
	d_deleted.clear();
    }

    // ensure that all embedded objects are deallocated eventually
    public void finalize() throws Throwable {
	try {
	    if (!isDeleted()) {
		assert(false);
//		System.out.println("EmbeddedManager.Finalizer: should never be called");
		throw new Error("EmbeddedManager.Finalizer: should never be called");
	    }
	} finally {
	    super.finalize();
	}
    }
}
