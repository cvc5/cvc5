Solvers & Results
===========================

Simple Solving
----------------

.. autofunction:: cvc5.pythonic.solve
.. autofunction:: cvc5.pythonic.solve_using
.. autofunction:: cvc5.pythonic.prove


The Solver Class
----------------

.. autofunction:: cvc5.pythonic.SolverFor

.. autofunction:: cvc5.pythonic.SimpleSolver

.. autoclass:: cvc5.pythonic.Solver
  :members:
  :special-members:

Results & Models
----------------
.. data:: cvc5.pythonic.unsat

  An *UNSAT* result.

.. data:: cvc5.pythonic.sat

  A *SAT* result.

.. data:: cvc5.pythonic.unknown

  The satisfiability could not be determined.

.. autoclass:: cvc5.pythonic.CheckSatResult
  :members:
  :special-members:

.. autoclass:: cvc5.pythonic.ModelRef
  :members:
  :special-members:

Utilities
--------------

.. autofunction:: cvc5.pythonic.evaluate
.. autofunction:: cvc5.pythonic.simplify
.. autofunction:: cvc5.pythonic.substitute
.. autofunction:: cvc5.pythonic.Sum
.. autofunction:: cvc5.pythonic.Product
