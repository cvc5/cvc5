Cvc5Statistics
==============

See :doc:`/statistics` for general information on statistics in cvc5.

Struct :cpp:struct:`cvc5::Statistics` represents a mapping from statistic names
to statistic values, which are represented by struct :cpp:type:`Cvc5Stat`. A
:cpp:type:`Cvc5Stat` may hold values of different
types (``bool``, ``int64_t``, ``uint64_t``, ``double``, ``const char*`` and
histograms) and can be inspected by identifying the type via functions
``cvc5_stat_is_<type>`` and obtaining
the actual value via functions ``cvc5_stat_get_<type>``.
Histograms are represented as a paar of arrays (``const char** keys[]`` and
``uint64_t* values[]``) where the key is the string representation of one
enumeration value and the value is the frequency of this particular value.

A statistics iterator can be initialized via :cpp:func:`cvc5_stats_iter_init()`,
which allows to configure the visbility of internal and unchanged statistic
entries. Iteration over statistics entries is then provided via functions
:cpp:func:`cvc5_stats_iter_has_next()` and :cpp:func:`cvc5_stats_iter_next()`.

.. container:: hide-toctree

  .. toctree::

----

.. doxygentypedef:: Cvc5Stat
    :project: cvc5_c

----

.. doxygengroup:: c_cvc5stat
    :project: cvc5_c
    :content-only:

----

.. doxygentypedef:: Cvc5Statistics
    :project: cvc5_c

----

.. doxygengroup:: c_cvc5statistics
    :project: cvc5_c
    :content-only:
