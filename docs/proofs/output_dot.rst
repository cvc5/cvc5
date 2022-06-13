Proof format: DOT
=================

Using the flag :ref:`proof-format-mode=dot <lbl-option-proof-format-mode>`, cvc5 outputs proofs in the DOT format.

The DOT format is a graph description language (see e.g. `this description <https://en.wikipedia.org/wiki/DOT_(graph_description_language)>`_). It can be used, among other things, for visualization.

We leverage this format for visualizing cvc5 proofs, in the internal calculus, as a graph. One can use a default dot visualizer or the dedicated proof visualizer `available here <https://ufmg-smite.github.io/proof-visualizer>`_. It suffices to upload the DOT proof outputted by cvc5, saved into a file. The visualizer offers several custom features, such as fold/unfold subproofs, coloring nodes, and stepwise expansion of let terms.
