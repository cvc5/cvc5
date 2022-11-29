from cvc5.pythonic import *

if __name__ == '__main__':
    # This example builds a simple "cons list" of integers, with
    # two constructors, "cons" and "nil."

    # Building a datatype consists of two steps.
    # First, the datatype is specified.
    # Second, it is "resolved" to an actual sort, at which point function
    # symbols are assigned to its constructors, selectors, and testers.

    decl = Datatype("list")
    decl.declare("cons", ("head", IntSort()), ("tail", decl))
    decl.declare("nil")
    List = decl.create()

    # Using constructors and selectors:
    t = List.cons(0, List.nil)
    print("t is:", t)
    print("head of t is:", List.head(t))
    print("after simplify:", simplify(List.head(t)))
    print()

    # You can iterate over constructors and selectors
    for i in range(List.num_constructors()):
        ctor = List.constructor(i)
        print("ctor:", ctor)
        for j in range(ctor.arity()):
            print(" + arg:", ctor.domain(j))
            print("   + selector:", List.accessor(i, j))
    print()

    # You can use testers
    print("t is a 'cons':", simplify(List.is_cons(t)))
    print()

    # This Python API does not support type parameters or updators for
    # datatypes. See the base Python API for those features, or construct them
    # using Python functions/classes.

    a = Int('a')
    solve(List.head(List.cons(a, List.nil)) > 50)

    prove(Not(List.is_nil(List.cons(a, List.nil))))
