package cvc3;

import java.util.*;

// used to enforce timeout in class Cvc3
class TimeoutHandler extends TimerTask {
    public void run() {
	System.out.println("self-timeout.");
	System.exit(1);
    }
}
