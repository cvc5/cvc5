Cvc5Result
==========

This class represents a :cpp:type:`Cvc5` result.

A :cpp:type:`Cvc5Result` encapsulates a 3-valued solver result (sat, unsat,
unknown). Explanations for unknown results are represented as enum class
:cpp:enum:`Cvc5UnknownExplanation` and can be queried via
:cpp:func:`cvc5_result_get_unknown_explanation()`.

.. container:: hide-toctree

  .. toctree::

----

.. doxygentypedef:: Cvc5Result
    :project: cvc5_c

----

.. doxygengroup:: c_cvc5result
    :project: cvc5_c
    :content-only:
