package cvc3;

import java.util.*;

class Cvc3 {
    static boolean useObjManager = false;

    static void timeoutHandler(Object o) {
      System.out.println("self-timeout.");
      System.exit(1);
    }

    public static void main(String args[]) throws Cvc3Exception {

	ValidityChecker vc = null;
	FlagsMut flags = null;
	try {
	    flags = ValidityChecker.createFlags(null);
	
	    // parse input
	    String fileName = "";
	    try {
		fileName = parse_args(args, flags);
	    } catch(CLException e) {
		System.err.print("*** " + e);
		System.err.println("\n\nRun with -help option for usage information.");
		System.exit(1);
	    }
	    
	    // Set the timeout, if given in the command line options
	    int timeout = flags.getFlag("timeout").getInt();
	    if (timeout > 0) {
		new Timer().schedule(new TimeoutHandler(), timeout * 1000);
	    }
	    
	    /*
	     * Create and run the validity checker
	     */ 
	    
	    // Debugging code may throw an exception
	    vc = ValidityChecker.create(flags);
	    flags.delete();

	    // -h flag sets "help" to false (+h would make it true, but that's
	    // not what the user normally types in).
	    if(!vc.getFlags().getFlag("help").getBool()) {
		String programName = "cvc3"; //:TODO:
		printUsage(vc.getFlags(), programName);
		System.exit(0);
	    }

	    // Similarly, -version sets the flag "version" to false
	    if(!vc.getFlags().getFlag("version").getBool()) {
		System.out.println("This is CVC3 version " + "UNKNOWN"); //:TODO:
		System.out.println("Copyright (C) 2003-2006 by the Board of Trustees of Leland Stanford Junior");
		System.out.println("University, New York University, and the University of Iowa.");
		System.out.println();
		System.out.print("THIS SOFTWARE PROVIDED AS-IS, WITHOUT ANY WARRANTIES. ");
		System.out.println("USE IT AT YOUR OWN RISK.");
		System.out.println();
		System.exit(0);
	    }

	    // Test if the output language is correctly specified; if not, an
	    // exception will be thrown
	    vc.getExprManager().getOutputLanguage();
	    // Read the input file
	    vc.loadFile(fileName, vc.getExprManager().getInputLanguage());
      
	    // Print statistics
	    if (vc.getFlags().getFlag("stats").getBool()) {
		vc.printStatistics();
	    }
	} catch (Cvc3Exception e) {
	    System.err.println("*** Fatal exception: " + e);
	    System.exit(1);
	} finally {
	    if (flags != null) flags.delete();
	    if (vc != null) vc.delete();
	}

	// to avoid waiting for timer to finish
	System.exit(0);
    }



    // evaluates command line flags, returns problem file name
    public static String parse_args(String[] args, FlagsMut flags) throws Cvc3Exception {
	// keep track that exactly one file name is given
	String fileName = "";
	boolean seenFileName = false;

	// iterate over the arguments
	for (int i = 0; i < args.length; ++i) {
	    String arg = args[i];

	    // A command-line option
	    if (arg.startsWith("-") || arg.startsWith("+")) {
		List names = flags.getFlags(arg.substring(1));

		// no match
		if (names.size() == 0)
		    throw new CLException(arg + " does not match any known option");

		// ambiguous
		else if (names.size() > 1) {
		    StringBuffer s = new StringBuffer();
		    s.append(arg + " is ambiguous.  Possible matches are:\n");
		    for (Iterator name = names.iterator(); name.hasNext(); ) {
			s.append("  " + name.next() + "\n");
		    }
		    throw new CLException(s.toString());
		}
			 
		// Single match; process the option by name, type, and parameters
		else {
		    String name = (String) names.iterator().next();
		    boolean val = arg.startsWith("+");
		    Flag flag = flags.getFlag(name);

		    if (flag.isBool()) {
			flags.setFlag(name, val);
		    }

		    else if (flag.isInt()) {
			++i;
			if (i >= args.length)
			    throw new CLException (arg + " (-" + name + ") expects an integer argument.");
			int parameter = Integer.parseInt(args[i]);
			flags.setFlag(name, parameter);
		    }

		    else if (flag.isString()) {
			++i;
			if (i >= args.length)
			    throw new CLException (arg + " (-" + name + ") expects a string argument.");
			flags.setFlag(name, args[i]);            
		    }

		    //             else if (flag.isStringVec())
		    //             {
		    //               bool hasMore = iter.MoveNext();
		    //               if (!hasMore)
		    //               {
		    //                 throw new CLException
		    //                   (arg + " (-" + name + ") expects a string argument.");
		    //               }
		    //               flags.setFlag(name, (string)iter.Current, val);
		    //             }
		    
		    else {
			throw new CLException("parse_args: Bad flag : " + name);
		    }
		}
	    }
        
	    // no flag, so should be a file name
	    // second no flag argument
	    else if(seenFileName) {
		throw new CLException("More than one file name given: " + fileName + " and " + arg);
	    }

	    // first no flag argument
	    else {
		fileName = arg;
		seenFileName = true;
	    }
	}

	return fileName;
     }


    public static void printUsage(Flags flags, String programName) throws Cvc3Exception {
	System.out.println("Usage: " + programName + " [options]");
	System.out.println(programName + " will read the input from STDIN and ");
	System.out.println("print the result on STDOUT.");
	System.out.println("Boolean (b) options are set 'on' by +option and 'off' by -option");
	System.out.println("(for instance, +sat or -sat).");
	System.out.println("Integer (i), string (s) and vector (v) options ");
	System.out.println("require a parameter, e.g. -width 80");
	System.out.println("Also, (v) options can appear multiple times setting args on and off,");
	System.out.println("as in +trace \"enable this\" -trace \"disable that\".");
	System.out.println("Option names can be abbreviated to the shortest unambiguous prefix.");
	System.out.println();
	System.out.println("The options are:");

	// Get all the names of options (they all match the empty string)
	List names = flags.getFlags("");
	for (Iterator i = names.iterator(); i.hasNext(); ) {
	    String name = (String) i.next();
	    Flag flag = flags.getFlag(name);
	    String prefix = "";
	    if (flag.isNull()) {
		prefix = " (null)";
	    }
	    else if (flag.isBool()) {
		String enabled = flag.getBool() ? "+" : "-";
		prefix = " (b) " + enabled + name;
	    }
	    else if (flag.isInt()) {
		prefix = " (i) -" + name + " " + flag.getInt();
	    }
	    else if (flag.isString()) {
		prefix = " (s) -" + name + " " + flag.getString();
	    }
	    else if (flag.isStringVec()) {
		prefix = " (s) -" + name;
	    }
	    else {
		assert(false);
	    }
	    
	    while (prefix.length() < 21) {
		prefix += " ";
	    }
	    System.out.println(prefix + " " + flag.getHelp());
	}
	System.out.println();
    }
}
