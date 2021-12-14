Theory of Relations
===================

This simple family example demonstrates theory of finite relations extension to the theory of finite sets.
Relations are defined as sets of tuples with arity :math:`\geq 1`.
We have unary relations :math:`people, males,` and :math:`females` of arity 1.
We also have binary relations :math:`father, mother, parent, ancestor`, and :math:`descendant` of arity 2.
Here we follow a prefix convention (i.e., :math:`R(x,y)` or
:math:`\langle x, y \rangle \in R` if and only if
person :math:`x` has relation `R` with person :math:`y`,
where :math:`R \in \{father, mother, parent, ancestor, descendant\}`.


We have the following list of constraints:

- All relations are nonempty.
- People is the universe set.
- Males and females are disjoint sets (i.e., :math:`males \cap females = \phi`).
- Fathers are males (i.e., :math:`father \bowtie people \subseteq males`).
- Mothers are females (i.e., :math:`mother \bowtie people \subseteq females`).
- A parent is a father or a mother (i.e., :math:`parent = father \cup mother`).
- Ancestor relation is the transitive closure of parent (i.e., :math:`ancestor = parent^{+}`).
- Descendant relation is the transpose of ancestor (i.e., :math:`descendant = ancestor^{-1}`).
- No self ancestor (i.e., :math:`\forall x: Person. \langle x, x \rangle \not\in ancestor`).

.. api-examples::
    <examples>/api/cpp/relations.cpp
    <examples>/api/java/Relations.java
    <examples>/api/python/relations.py
    <examples>/api/smtlib/relations.smt2

