Cvc5Kind
========

Every :cpp:type:`Cvc5Term` has an associated kind, represented
as enum :cpp:enum:`Cvc5Kind`.
This kind distinguishes if the term is a value, constant, variable or operator,
and what kind of each.
For example, a bit-vector value has kind
:cpp:enumerator:`CVC5_KIND_CONST_BITVECTOR`, a free constant symbol has kind
:cpp:enumerator:`CVC5_KIND_CONSTANT`,
an equality over terms of any sort has kind :cpp:enumerator:`CVC5_KIND_EQUAL`,
and a universally quantified formula has kind
:cpp:enumerator:`CVC5_KIND_FORALL`.

.. container:: hide-toctree

  .. toctree::

----

.. doxygenenum:: Cvc5Kind
    :project: cvc5_c

----

.. doxygenfunction:: cvc5_kind_to_string
    :project: cvc5_c

.. doxygenfunction:: cvc5_kind_hash
    :project: cvc5_c
