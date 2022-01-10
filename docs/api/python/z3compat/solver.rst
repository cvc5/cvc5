Solvers & Results
===========================

Simple Solving
----------------

.. autofunction:: cvc5_z3py_compat.solve
.. autofunction:: cvc5_z3py_compat.solve_using
.. autofunction:: cvc5_z3py_compat.prove


The Solver Class
----------------

.. autofunction:: cvc5_z3py_compat.SolverFor

.. autofunction:: cvc5_z3py_compat.SimpleSolver

.. autoclass:: cvc5_z3py_compat.Solver
  :members:
  :special-members:

Results & Models
----------------
.. data:: cvc5_z3py_compat.unsat

  An *UNSAT* result.

.. data:: cvc5_z3py_compat.sat

  A *SAT* result.

.. data:: cvc5_z3py_compat.unknown

  The satisfiability could not be determined.

.. autoclass:: cvc5_z3py_compat.CheckSatResult
  :members:
  :special-members:

.. autoclass:: cvc5_z3py_compat.ModelRef
  :members:
  :special-members:

Utilities
--------------

.. autofunction:: cvc5_z3py_compat.evaluate
.. autofunction:: cvc5_z3py_compat.simplify
.. autofunction:: cvc5_z3py_compat.substitute
.. autofunction:: cvc5_z3py_compat.Sum
.. autofunction:: cvc5_z3py_compat.Product
