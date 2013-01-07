#!/usr/bin/python

import os, sys, tempfile, random, subprocess

from optparse import OptionParser

# Create the options parser
def create_parser():
    global parser
    parser = OptionParser(usage = "%prog [options]") 
    parser.add_option("-n", "--size", type="int", action="store", dest="size", default="1", help="size of the problem")

# The main code
def main():
    global opts, args
    # Create the parser
    create_parser()
    # Parse program arguments
    (opts, args) = parser.parse_args()
    # Run the main loop
    generate()    

def generate():
    # Preamble
    print "(set-logic QF_LRA)"
    print "(set-info :smt-lib-version 2.0)"
    # Variables
    for var in range(opts.size+1):
      print "(declare-fun a%d () Real)" % var
      print "(declare-fun b%d () Real)" % var
      print "(declare-fun c%d () Real)" % var
    # Forward edges 
    for var in range(opts.size):
      print "(assert (or (and (< a%d b%d) (< b%d a%d)) (and (< a%d c%d) (< c%d a%d))))" % (var, var, var, var+1, var, var, var, var+1)  
    # Back edge
    print "(assert (> a0 a%d))" % opts.size
    # Finish
    print "(check-sat)"
    print "(exit)"
        
# Run the main
if __name__ == "__main__":
    main()

