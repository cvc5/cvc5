#!/usr/bin/python

import os, sys, tempfile, random, subprocess

from optparse import OptionParser

# Create the options parser
def create_parser():
    global parser
    parser = OptionParser(usage = "%prog [options]") 
    parser.add_option("-o", "--output-dir", action="store", dest="output_dir", default=".", help="directory in which to store the wrong results")
    parser.add_option("-g", "--golden-solver", action="store", dest="golden_solver", default=None, help="solver that you can trust")
    parser.add_option("-s", "--solver", action="store", dest="solver", default=None, help="solver that you are testing")
    parser.add_option("-l", "--limit", type="int", action="store", dest="limit", default="1", help="limit the number of (wrong) problems")
    parser.add_option("-v", "--vars", type="int", action="store", dest="vars", default="5", help="number of variables to use")
    parser.add_option("-a", "--atoms", type="int", action="store", dest="atoms", default="5", help="number of atoms to generate")
    parser.add_option("-c", "--clauses", type="int", action="store", dest="clauses", default="5", help="number of constraints to create")
    parser.add_option("-C", "--clause-size", type="int", action="store", dest="clause_size", default="5", help="limit the number of variables per clause")
    parser.add_option("-L", "--logic", action="store", dest="logic", help="the logic")

# The main code
def main():
    global opts, args
    # Create the parser
    create_parser()
    # Parse program arguments
    (opts, args) = parser.parse_args()
    # Chang directory to the working directory
    os.chdir(opts.output_dir)    
    # Run the main loop
    main_loop()    

def generate_LRA():
    size = random.randint(1, opts.vars)
    selection = random.sample(range(opts.vars), size)
    
    ops = ["<", "<=", "=", ">=", ">"]
    
    # Start constraint
    constraint = "("
    # Add the operation
    constraint += random.choice(ops) 
    
    # Linear combination
    constraint += " (+"
    for var in selection:
        coeff = random.randint(1, 10)
        coeff_negated = random.randint(0, 1)
        if (coeff_negated == 0):
            constraint += " (* %d x%d)" % (coeff, var)
        else:
            constraint += " (* (- %d) x%d)" % (coeff, var)
    # Constant
    coeff = random.randint(0, 10)
    coeff_negated = random.randint(0, 1)
    if (coeff_negated == 0):
        constraint += " %d" % coeff
    else:
        constraint += " (- %d)" % coeff
    # End the linear combination
    constraint += ")"
    
    # End the constraint 
    constraint += " 0)"
    
    return constraint

def generate_atoms(logic):
    global atoms;
    atoms = [];
    
    if logic == "QF_SAT":
        for var in range(0, opts.vars):
            atoms.append("x%d" % var)
    elif logic == "QF_LRA":
        for atom in range(0, opts.atoms):
            atoms.append(generate_LRA())

def mk_clause(file):
    # Random size
    size = random.randint(1, opts.clause_size)
    # Random selection of atoms
    selection = random.sample(atoms, size)
    # Begin assertion and an or
    file.write("(assert")
    if size > 1:
        file.write(" (or")
    # Generate literals
    for atom in selection:
       if random.randint(0, 1) == 1:
           file.write(" (not %s)" % atom)           
       else:
           file.write(" %s" % atom)
    # End assertion and the or
    if size > 1:
       file.write(")")
    file.write(")\n")

def get_type(logic):
    if logic == "QF_SAT":
        return "Bool";
    elif logic == "QF_LRA":
        return "Real";
    else:
        return Unknown;

def mk_problem(file):
    # Preamble
    file.write("(set-logic %s)\n" % opts.logic)
    file.write("(set-info :smt-lib-version 2.0)\n")
    # Variables
    type = get_type(opts.logic); 
    for var in range(opts.vars):
        file.write("(declare-fun x%d () %s)\n" % (var, type))
    # Clauses 
    generate_atoms(opts.logic)
    for clause in range(opts.clauses):
	mk_clause(file)
    # Finish
    file.write("(check-sat)\n")
    file.write("(exit)\n")

def main_loop():
    # No problems yet
    problems = 0;
    while problems < opts.limit:
        # Open the first file
        (fd, path) = tempfile.mkstemp(suffix=".smt2", dir=opts.output_dir, text=True)
        file = os.fdopen(fd, "w")
        # Create a problem instance
        mk_problem(file)    
        # Close the file
        file.close()
        
        if opts.golden_solver is not None:
            # Execute the golden solver
            golden_exec = [opts.golden_solver, path]
            try:
                golden_solver_output = subprocess.check_output(golden_exec).strip()
            except subprocess.CalledProcessError as e:
                golden_solver_output = e.output.strip()        
        
        if opts.solver is not None:
            # Execute the test solver 
            solver_exec = [opts.solver, path]
            try:
                solver_output = subprocess.check_output(solver_exec).strip()
            except subprocess.CalledProcessError as e:
                solver_output = e.output.strip()           
        
        if (opts.golden_solver is not None) and (opts.solver is not None): 
            if golden_solver_output == solver_output:
                os.remove(path);
                sys.stderr.write("%s " % solver_output)
            else:
                sys.stderr.write("WRONG ")
                problems = problems + 1
        else:
            problems = problems + 1 
        
# Run the main
if __name__ == "__main__":
    main()

