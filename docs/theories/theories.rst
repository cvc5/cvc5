Theory References
=================

cvc5 supports all theories that are currently standardized in SMT-LIB.
Additionally, it also implements several theories that are not (yet)
standardized, or that extend beyond the respective standardized theory.
Furthermore, cvc5 supports all combinations of all implemented theories as well
as combinations with `datatypes, quantifiers, and uninterpreted functions (as
defined in the SMT-LIB standard)
<https://smt-lib.org/language.shtml>`_.

Standardized theories
---------------------

.. toctree::
   :maxdepth: 1

   Theory of arrays <https://smt-lib.org/theories-ArraysEx.shtml>
   Theory of bit-vectors <https://smt-lib.org/theories-FixedSizeBitVectors.shtml>
   Theory of floating-point numbers <https://smt-lib.org/theories-FloatingPoint.shtml>
   Theory of integer arithmetic <https://smt-lib.org/theories-Ints.shtml>
   Theory of real arithmetic <https://smt-lib.org/theories-Reals.shtml>
   Theory of mixed-integer arithmetic <https://smt-lib.org/theories-Reals_Ints.shtml>
   Theory of strings <https://smt-lib.org/theories-UnicodeStrings.shtml>

Non-standard or extended theories
---------------------------------

.. toctree::
   :maxdepth: 1

   bags
   datatypes
   finite_field
   separation-logic
   sequences
   sets-and-relations
   strings
   transcendentals
