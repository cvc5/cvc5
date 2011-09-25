package cvc3;


/** mirrors CVC3::Exception */
public class Cvc3Exception extends RuntimeException {

    private final static long serialVersionUID = 1L;

    public Cvc3Exception(String message) {
	super(message);
    }
}
