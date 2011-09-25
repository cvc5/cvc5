package cvc3;

import java.util.*;

/** mirrors CVC3::SoundException */
public class SoundException extends Cvc3Exception {

    private final static long serialVersionUID = 1L;

    public SoundException(String message) {
	super(message);
    }
}
