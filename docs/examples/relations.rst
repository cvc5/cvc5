Theory of Relations
===================

This simple example demonstrates the combined
`theory of finite sets and finite relations <../theories/sets-and-relations.html>`_ using a family tree.
Relations are defined as sets of tuples with arity :math:`\geq 1`.
The example includes the unary relations :math:`people, males,` and  :math:`females`
and the binary relations :math:`father, mother, parent, ancestor`, and :math:`descendant`.


We have the following list of constraints:

- All relations are nonempty.
- People is the universe set.
- Males and females are disjoint sets (i.e., :math:`males \cap females = \phi`).
- Fathers are males (i.e., :math:`father \bowtie people \subseteq males`) [*]_.
- Mothers are females (i.e., :math:`mother \bowtie people \subseteq females`).
- A parent is a father or a mother (i.e., :math:`parent = father \cup mother`).
- Ancestor relation is the transitive closure of parent (i.e., :math:`ancestor = parent^{+}`).
- Descendant relation is the transpose of ancestor (i.e., :math:`descendant = ancestor^{-1}`).
- No self ancestor (i.e., :math:`\forall x: Person. \langle x, x \rangle \not\in ancestor`).

.. [*] :math:`\bowtie` denotes the relational join operator as defined in :cite:`MengRTB17`.

.. api-examples::
    <examples>/api/cpp/relations.cpp
    <examples>/api/java/Relations.java
    <examples>/api/python/relations.py
    <examples>/api/smtlib/relations.smt2

