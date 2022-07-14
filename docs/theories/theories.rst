Theory References
=================

cvc5 supports all theories that are currently standardized in SMT-LIB.
Additionally, it also implements several theories that are not (yet)
standardized, or that extend beyond the respective standardized theory.
Furthermore, cvc5 supports all combinations of all implemented theories as well
as combinations with `datatypes, quantifiers, and uninterpreted functions (as
defined in the SMT-LIB standard)
<https://smtlib.cs.uiowa.edu/language.shtml>`_.

Standardized theories
---------------------

.. toctree::
   :maxdepth: 1

   Theory of arrays <https://smtlib.cs.uiowa.edu/theories-ArraysEx.shtml>
   Theory of bit-vectors <https://smtlib.cs.uiowa.edu/theories-FixedSizeBitVectors.shtml>
   Theory of floating-point numbers <https://smtlib.cs.uiowa.edu/theories-FloatingPoint.shtml>
   Theory of integer arithmetic <https://smtlib.cs.uiowa.edu/theories-Ints.shtml>
   Theory of real arithmetic <https://smtlib.cs.uiowa.edu/theories-Reals.shtml>
   Theory of mixed-integer arithmetic <https://smtlib.cs.uiowa.edu/theories-Reals_Ints.shtml>
   Theory of strings <https://smtlib.cs.uiowa.edu/theories-UnicodeStrings.shtml>

Non-standard or extended theories
---------------------------------

.. toctree::
   :maxdepth: 1

   bags
   datatypes
   separation-logic
   sequences
   sets-and-relations
   strings
   transcendentals
